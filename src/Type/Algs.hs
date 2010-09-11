module Type.Algs 
  ( solveGoals, simplify, withSkolems, depsOf, closureFrom
  , instantiate, instantiate', generalize, generalize', noSkolems
  , nicerPreds, nicerPoly
  , unify, unifyWith, match 
  ) where

import AST
import Error
import Type.Monad
import Type.Error
import Type.FVS
import Type.Subst
import Opts(maxWidth)

import Utils
import Data.List (partition,nub)
import MonadLib hiding(collect)


-- Skolem constants (i.e., variable that cannot be bound to anything)
type SolverM        = ReaderT [TyVar] TypeM

withSkolems        :: [TyVar] -> SolverM a -> TypeM a
withSkolems xs m    = runReaderT xs m

noSkolems          :: SolverM a -> TypeM a
noSkolems m         = withSkolems [] m

err' x              = lift (err x)


-- Predicate solver ------------------------------------------------------------

solveGoals :: [Goal] -> [DGoal] -> TypeM ()
solveGoals gs1 gs2  = loop (DGoal [] (mono gs1) : gs2) [] False 
  where
  loop :: [DGoal] -> [DGoal] -> Bool -> TypeM ()
  loop [] [] _        = return ()
  loop [] todo True   = loop todo [] False
  loop [] todo False  = errs [ CannotSolve xs ps (map goalPred gs)
                              | DGoal _ (Forall xs ps gs) <- todo ]
  loop (DGoal es p : gs) todo ch1
    = do let asmps = zip es (polyPreds p)
             xs    = polyVars p
         (qs,ch2) <- withSkolems xs
                   $ simplify True asmps (poly p)
         let ch = ch1 || ch2
         case qs of
           [] -> loop gs todo ch
           _  -> loop gs (DGoal es (p { poly = qs }) : todo) ch


nicerPreds     :: [Pred] -> TypeM [Pred]
nicerPreds ps   = do (_,gs) <- collect $ forEach ps newEv
                     map goalPred # nicerGoals gs

nicerPoly                  :: Poly t -> TypeM (Poly t)
nicerPoly (Forall xs ps t)  = do ps <- nicerPreds ps
                                 xs <- inBase (nub # fvs (map TFree xs))
                                 let b = Forall xs ps t
                                 return b


-- | Compute an equavalent but simpler set of goals.
--   - Uses improvement to defined variables.
--   - Removes duplicates an superclasses.
--   - Removes things that can be solved by instances with no context.
nicerGoals     :: [Goal] -> TypeM [Goal]
nicerGoals gs   = noSkolems (fst # simplify {-False-} True [] gs)



-- Property: Does not produce output (Maybe enforce with types?)
-- Returns new list of goals, and if we bound any vars.
simplify :: Bool -> [(Ev,Pred)] -> [Goal] -> SolverM ([Goal], Bool)
simplify subs as gs  = do bs <- lift $ forEach gs g2a
                          loop as bs gs [] False
  where
  g2a (Ev d p)  = do e <- evFor d
                     return (e,p)

  -- as: assumptions
  -- bs: goals paired with their (future) evidence (lazy, recursion)
  -- gs: the goals we need to solve (not tried yet)
  -- todo: goals that we failed to solve
  -- ch: did anything change?

  -- if something changed, we try again...
  loop _ _ [] todo ch = if ch then do (gs,_) <- simplify subs as todo
                                      return (gs,True)
                              else return (todo, False)

  -- ... when we solve a goal we use the assumptions,
  -- and all the remaining goals, as eventually they should be solved:
  loop as (b:bs) (g:gs) todo ch1 
    = do ((sol,ch2),gs2) <- do sko <- ask
                               lift $ collect $ withSkolems sko 
                                    $ entail subs (bs++as) g   -- not pretty
         let ch = ch1 || ch2
         if sol then do bs' <- lift $ forEach gs2 g2a 
                        loop as (bs'++bs) (gs2++gs) todo ch
                else loop (b:as) bs gs (g:todo) ch

  -- ... othrwerwise there was a mismatch between the goals and their solns?
  loop _ _ _ _ _  = bug "simplfy.loop" "oops"
                                 




-- Returns (Solved?, changes?)
entail     :: Bool -> [(Ev,Pred)] -> Goal -> SolverM (Bool,Bool)
entail subs ps g = do ch <- improve (goalPred g)
                      loop ch ps g
  where 
  loop ch (p:ps) g  = do ch' <- impByPred (snd p) (goalPred g)
                         sol <- lift (solByAsmp p g `orM` solBySuper p g )
                         let ch'' = ch || ch'
                         if sol then return (sol,ch'')
                                else loop ch'' ps g
  loop ch [] g      = do sol <- lift (solByAxiom g `orM` solByInst subs g)
                         return (sol,ch)





-- Different tactics for solving predicates ------------------------------------

{- General notes about tactics:

    - Tactics return 'True' if they succeed and 'False' if they fail.
    - Tactics do not do improvement.  
    - Some tactics (currently 'byInst', 'byRule') may generate new sub-goals.
-}

-- | Try to use an assumption.
solByAsmp :: (Ev,Pred) -> Goal -> TypeM Bool
solByAsmp (e,p) (Ev d q)  = inBase (sameIO p q) `andM`
                            do addEvDef d e
                               return True
                              

-- | Try to use a super-class rule.
solBySuper :: (Ev,Pred) -> Goal -> TypeM Bool
solBySuper (e,CIn c ts) (Ev d (CIn c' ts')) 
  = (anyM . map try) =<< getSuperRules c
  where 
  try r = case ruleHead r of
            CIn c'' _ | c' == c'' -> 
              do (_,[CIn _ ts1],CIn _ ts2) <- instantiate' (rulePred r)
                 (and # forEach2 ts1 ts match) `andM`  
                   (inBase (and # forEach2 ts2 ts' sameIO)) `andM`
                   do addEvDef d (ruleProof r [e])
                      return True
            _ -> return False

         
-- | Try to use instances to solve goal.
-- The boolean indicates if we should be "agressive" (i.e. use instances with
-- context in predicates that contain variables)
solByInst :: Bool -> Goal -> TypeM Bool
solByInst subs g@(Ev _ (CIn c _)) = do is <- getInstances c
                                       anyM [ solByRule subs i g | i <- is ] 

-- | Solve by MP.  The sub-goals are implicitly added to the monad.
-- The boolean argument indicate if we should use rules that generate sub-goals
solByRule :: Bool -> Rule -> Goal -> TypeM Bool
solByRule agressive r (Ev d (CIn c ts)) 
  = ruleOK `andM` do (_,ps,CIn _ ts') <- instantiate' (rulePred r)
                     allM (zipWith match ts' ts) `andM`
                       do es <- forEach ps newEv
                          addEvDef d (ruleProof r es)
                          return True 
  where 
  Forall _ ctxt (CIn c' _)  = rulePred r 

  ruleOK | c /= c'          = return False
         | agressive        = return True
         | null ctxt        = return True
         | otherwise        = null # inBase (fvs ts)


-- | Try to use an axiom.
solByAxiom :: Goal -> TypeM Bool
solByAxiom g = byAx =<< inBase (pruneIO True g)
  where 
  byAx (Ev d (CIn pred args)) 
  
    | pred == cAdd
      = case args of
          -- x + y = z (for concrete x,y,z)
          [TCon (TNat x), TCon (TNat y), TCon (TNat z)]
            | x + y == z 
               -> do addEvDef d dummyEv
                     return True

          -- 0 + x = x
          [TCon (TNat 0), t2, t3]
            -> do same <- inBase (sameIO t2 t3)
                  if same then do addEvDef d dummyEv
                                  return True
                          else return False

          -- x + 0 = x
          [t1, TCon (TNat 0), t3]
            -> do same <- inBase (sameIO t1 t3)
                  if same then do addEvDef d dummyEv
                                  return True
                          else return False

          _ -> return False


    | pred == cTimes
      = case args of
          -- x * y = z (for concrete x,y,z)
          [TCon (TNat x), TCon (TNat y), TCon (TNat z)]
            | x * y == z 
               -> do addEvDef d dummyEv
                     return True

          -- 0 * x = 0
          [TCon (TNat 0), _, TCon (TNat 0)] -> do addEvDef d dummyEv
                                                  return True

          -- x * 0 = 0
          [_, TCon (TNat 0), TCon (TNat 0)] -> do addEvDef d dummyEv
                                                  return True

          -- 1 * x = x
          [TCon (TNat 1), t2, t3]
            -> inBase (sameIO t2 t3) `andM` (addEvDef d dummyEv >> return True)

          -- x * 1 = x
          [t1, TCon (TNat 1), t3]
            -> inBase (sameIO t1 t3) `andM` (addEvDef d dummyEv >> return True)

          _ -> return False


    | pred == cExp2
      = case args of
          -- 2 ^ x = y
          [TCon (TNat x), TCon (TNat y)]
            | 2 ^ x == y
               -> do addEvDef d dummyEv
                     return True

          _ -> return False

    | pred == cGCD
      = case args of
        -- GCD x y z    (gcd x y = z, for concrete x y z)
        [TCon (TNat x), TCon (TNat y), TCon (TNat z)]
          | gcd x y == z  -> do addEvDef d dummyEv 
                                return True
          | otherwise     -> return False

        -- GCD 1 t 1
        [TCon (TNat 1), _, TCon (TNat 1)] -> do addEvDef d dummyEv 
                                                return True

        -- GCD t 1 1
        [_, TCon (TNat 1), TCon (TNat 1)] -> do addEvDef d dummyEv 
                                                return True
        -- GCD 0 t t
        [TCon (TNat 0), t1, t2] 
          -> inBase (sameIO t1 t2) `andM` (addEvDef d dummyEv >> return True)

        -- GCD t 0 t
        [t1, TCon (TNat 0), t2]
          -> inBase (sameIO t1 t2) `andM` (addEvDef d dummyEv >> return True)

        -- GCD t t t
        [x,y,z] -> inBase (sameIO x y) `andM`
                   inBase (sameIO x z) `andM`
                   do addEvDef d dummyEv
                      return True

        _ -> return False


    | pred == cDNat 
      = case args of 
          [TCon (TNat x)] -> do addEvDef d (IntEv x)
                                return True
          _ -> return False


    -- Width n    (0 <= n <= maxWidth)
    | pred == cWidth 
      = case args of
          [TCon (TNat x)] | x <= maxWidth -> do addEvDef d (IntEv x)
                                                return True
          _ -> return False

    -- Index n    (1 <= n <= 2^(MaxWidth-1)-1)
    | pred == cIndex
      = case args of
          [TCon (TNat x)] | 1 <= x && x <= 2^(maxWidth-1)-1
            -> do addEvDef d (IntEv x)
                  return True
          _ -> return False

    -- Align n    (n = 2 ^ k, Width k)
    | pred == cAlign 
      = case args of
          [TCon (TNat x)] -> case lg2 x of
                               Just m | m <= maxWidth -> do addEvDef d (IntEv x)
                                                            return True
                               _ -> return False
          _ -> return False

    | otherwise = return False
 





-- Improvement -----------------------------------------------------------------

-- Returns 'True' if any vars got defined, otherwise 'False'.
improve :: Pred -> SolverM Bool
improve p = imp =<< inBase (pruneIO True p)
  where
  imp p@(CIn pred args) 

    | pred == cAdd
      = case args of
          -- 0 + t2 = t3  --> t2 == t3
          [TCon (TNat 0), t2, t3] -> unify' t2 t3

          -- t1 + 0 = t3  --> t1 == t3
          [t1, TCon (TNat 0), t3] ->  unify' t1 t3

          -- t1 + t2 = 0  -> t1 == 0, t2 == 0
          [t1, t2, TCon (TNat 0)] -> (||) # unify' t1 (tNat 0) 
                                         <# unify' t2 (tNat 0)

          -- x + y = t3 --> t3 == x + y 
          [TCon (TNat x), TCon (TNat y), t3] -> unify' t3 (tNat (x+y))

          -- x + t2 = z --> t2 == z - x  (if z >= x)
          [TCon (TNat x), t2, TCon (TNat z)]
            | z >= x    -> unify' t2 (tNat (z-x))
            | otherwise -> err' (CannotSolve [] [] [p])

          -- t1 + y = z --> t1 == z - y (if z >= y)
          [t1, TCon (TNat y), TCon (TNat z)]
            | z >= y    -> unify' t1 (tNat (z-y))
            | otherwise -> err' (CannotSolve [] [] [p])

          _ -> return False

    | pred == cTimes
      = case args of
          -- 1 * t2 = t3  --> t2 == t3
          [TCon (TNat 1), t2, t3] -> unify' t2 t3

          -- t1 * 1 = t3  --> t1 == t3
          [t1, TCon (TNat 1), t3] ->  unify' t1 t3

          -- 0 * t2 = t3  --> t3 = 0
          [TCon (TNat 0), _, t3] -> unify' t3 (tNat 0)

          -- t1 * 0 = t3  --> t3 = 0
          [_, TCon (TNat 0), t3] ->  unify' t3 (tNat 0)

          -- t1 * t2 = 1  -> t1 == 1, t2 == 1
          [t1, t2, TCon (TNat 1)] -> (||) # unify' t1 (tNat 1) 
                                         <# unify' t2 (tNat 1)

          -- x * y = t3 --> t3 == x * y 
          [TCon (TNat x), TCon (TNat y), t3] -> unify' t3 (tNat (x*y))

          -- x * t2 = z --> t2 == z / x  (if there's no reminder)
          [TCon (TNat x), t2, TCon (TNat z)]
            -> case z `divMod` x of
                 (a,0) -> unify' t2 (tNat a)
                 _     -> err' (CannotSolve [] [] [p])

          -- t1 * y = z --> t1 == z / y (if there's no reminder)
          [t1, TCon (TNat y), TCon (TNat z)]
            -> case z `divMod` y of
                 (a,0) -> unify' t1 (tNat a)
                 _     -> err' (CannotSolve [] [] [p])

          _ -> return False


    | pred == cExp2
      = case args of 
          -- 2 ^ x = t2 --> t2 == 2^x
          [TCon (TNat x), t2] -> unify' t2 (tNat (2^x))

          -- 2 ^ t1 = x --> t1 == log x (of ok)
          [t1, TCon (TNat x)] 
            -> case lg2 x of
                 Just a -> unify' t1 (tNat a)
                 _      -> err' (CannotSolve [] [] [p])

          _ -> return False

    | pred == cGCD
      = case args of
          -- GCD x y t --> t == gcd x y
          [TCon (TNat x), TCon (TNat y), t] -> unify' t (tNat (gcd x y))

          -- GCD 0 x y --> x == y
          [TCon (TNat 0), x, y] -> unify' x y

          -- GCD x 0 y --> x == y
          [x, TCon (TNat 0), y] -> unify' x y

          -- GCD 1 x y --> y == 1
          [TCon (TNat 1), _, y] -> unify' (tNat 1) y

          -- GCD x 1 y --> y == 1
          [_, TCon (TNat 1), y] -> unify' (tNat 1) y

          _ -> return False

    | otherwise = impByInst p



-- | Improve a predicate based on the instances we have in the database
impByInst            :: Pred -> SolverM Bool
impByInst (CIn c ts)  = do is  <- lift $ getInstances c
                           fds <- lift $ getFDs c
                           loop False fds [ p | r <- is, let p = rulePred r ]
                                              -- , null (polyPreds p) ]
  where
  -- ch: did something change?
  -- fs: FDs that have not yet fired
  -- is: instances that we have not yet examined
  loop ch [] _        = return ch
  loop ch _ []        = return ch
  loop ch fs (i:is)   = do (_,_,CIn _ ts') <- lift $ instantiate' i
                  
                           (ch',fs') <- impByFDs True ts' ts fs

                            -- XXX
                            -- This may report "fake" changes leading to loops.
                            -- This happens when we unify a variable
                            -- in 'ts' with a fresh variable.

                            -- We need to "direct" information flow
                            -- from instance to goal.
                           loop (ch || ch') fs' is      
                           
       

impByPred            :: Pred -> Pred -> SolverM Bool
impByPred (CIn c ts) (CIn c' ts')
  | c == c'           = do fds   <- lift $ getFDs c
                           (b,_) <- impByFDs False ts ts' fds
                           return b

impByPred _ _         = return False




-- | Use some FDs for improvement.
-- We return: (if anything changed, FDs that didn't fire)
impByFDs :: Bool -> [Type] -> [Type] -> [FunDep'] -> SolverM (Bool,[FunDep'])
impByFDs byInst ts1 ts2 fds = loop False False [] fds
  where
  -- chTot: did anything change overall (True if we loop more than once)
  -- ch: did anything change this time around
  -- xs: fundeps that didn't fire
  loop chTot ch xs (fd:fds) = do x <- impByFD byInst fd ts1 ts2
                                 case x of
                                   Nothing -> loop chTot ch (fd:xs) fds
                                   Just b -> loop chTot (b || ch) xs fds
  -- we can avoid this looping by computing a closure on the FDs
  -- once in the class.
  loop chTot ch xs [] 
    | ch              = loop True False [] xs
    | otherwise       = return (chTot,xs)


-- | Use a functional dependency to do some improvement.
-- Returns:
--   * Nothing: the FD didn't 'fire'
--   * Just b: the FD 'fired', and 'b' is if anything changed.
impByFD  :: Bool -> FunDep' -> [Type] -> [Type] -> SolverM (Maybe Bool)
impByFD byInst (xs,ys) ts1 ts2 
  = ifM (allM (zipWith sim (types ts1 xs) (types ts2 xs)))
       ((Just . or) # forEach2 (types ts1 ys) (types ts2 ys) uni)
       (return Nothing)
  where 
  types ts xs     = map (ts !!) xs

  uni t1 t2 | byInst    = do (_,y) <- unify2 t1 t2
                             return y
            | otherwise = unify' t1 t2 

  sim t1 t2 | byInst    = lift $ match t1 t2                      
            | otherwise = inBase $ sameIO t1 t2


-- XXX
-- Functional dependencies -----------------------------------------------------

type FunDep         = ([TyVar], [TyVar])

funDeps            :: Name -> [[TyVar]] -> TypeM [FunDep]
funDeps pred args   = do fds <- getFDs pred
                         return (map cvt fds)
  where
  toSet xs          = concat (map (args !!) xs)
  cvt (xs,ys)       = (toSet xs, toSet ys)



closureFrom              :: [FunDep] -> [TyVar] -> [TyVar]
closureFrom fds zs   
  | vs `subset` zs        = zs
  | otherwise             = closureFrom fds' (zs ++ vs)
  where (fire, fds')      = partition ((`subset` zs) . fst) fds
        vs                = concat (map snd fire)
        xs `subset` ys    = all (`elem` ys) xs

-- | Returns the free variables of each predicate, 
-- and the functional dependecies that we get from the predicates.
depsOf           :: [Pred] -> TypeM ([[TyVar]], [FunDep])
depsOf ps         = do vs <- inBase (forEach ps fvsArgs) 
                       ds <- concat # forEach2 [c | CIn c _ <- ps] vs funDeps 
                       return (map concat vs,ds)



-- Schemas ---------------------------------------------------------------------

instantiate'      :: Subst p => Poly p -> TypeM ([TyVar],[Pred],p)
instantiate' (Forall [] ps t) = return ([],ps,t)
instantiate' (Forall xs ps t)
                  = do as <- forEach xs freshTVar
                       let sub = listSubst (zip xs (map TFree as))
                       t  <- subst sub t
                       ps <- forEach ps (subst sub)
                       return (as,ps,t)

instantiate      :: Subst p => Poly p -> TypeM ([TyVar],[Ev],p)
instantiate p     = do (as,ps,t) <- instantiate' p
                       ds <- forEach ps newEv
                       return (as,ds,t)

-- | Generalize a number of types.
-- Arguments:
-- * The 'xs' are variables that should be generalized in all schemas.
--    We check that the 'xs' are indeed generic variables.
-- * The 'goals' are a set of predicates that we have collected.  Some of
--      them will end up in the schema (if they mention generic variables).
-- * The 'ts' are the types that need to be turned into schemas.
--
-- Results: 
--  * the 'goals' that ended up in the schemas and should become args.
--  * The new schemas.
--
-- Side effects: 
--  * We add definitions for goals that we could solve.
--  * We output goals that we could not solve, but they don't mention generic
--    variables, and so can be processed later.

generalize'       :: [TyVar] -> [Goal] -> [Type] -> TypeM ([Goal],[Schema])
generalize' xs goals ts = 
  do goals         <- nicerGoals goals
     let ps         = map goalPred goals
     asmVars       <- freeInEnv 
     (predVarss,deps) <- depsOf ps
     let fixedVars  = closureFrom deps asmVars
         badVars    = [ x | x <- xs, x `elem` fixedVars ]

     when (not (null badVars)) $ err (CannotGeneralize badVars)

     tyVarss <- inBase (forEach ts fvs)
     let predVars       = concat predVarss
         (ngpvs, gpvs)  = partition (`elem` fixedVars) predVars
         gpvs'          = gpvs ++ xs

         genVarss = [ nub (filter (`notElem` fixedVars) vs ++ gpvs') 
                                                            | vs <- tyVarss ]
         genVars            = concat genVarss
         isLocal (vs,_)     = any (`elem` genVars) vs
         (forHere,forLater) = partition isLocal (zip predVarss goals)

     delayL (map snd forLater)
     schemas <- forEach3 genVarss tyVarss ts $ \xs vs t ->
        do let ambigs = ambiguousGoals deps xs (vs ++ ngpvs) forHere
           when (not (null ambigs)) $ errs $ map AmbiguousPredicate ambigs
           return (Forall xs (map (goalPred . snd) forHere) t)

     return (map snd forHere, schemas)


generalize :: [Goal] -> [Type] -> TypeM ([Goal],[Schema]) 
generalize = generalize' []


-- | A variable in a predicate is ambiguous, if it gets generalized,
-- but cannot be determined by any of the variables in the corresponding type
-- together with variables that are free in the env.
ambiguousVars funDeps genVars tyVars predVars = 
  [ x | x <- predVars, x `elem` genVars, not (x `elem` det) ]
  where det = closureFrom funDeps tyVars


-- Compute ambiguous goals that are about to be generalized.
ambiguousGoals funDeps genVars tyVars goals =
  [ goalPred goal | 
        (predVars, goal) <- goals,
        let ambigs = ambiguousVars funDeps genVars tyVars predVars,
        not (null ambigs) ]
  


-- Unification -----------------------------------------------------------------

unify              :: Type -> Type -> TypeM ()
unify s t           = do s <- inBase (pruneIO False s)
                         t <- inBase (pruneIO False t)
                         uni s t
  where
  uni (TFree x) t   = bindVar x t >> return ()
  uni t (TFree x)   = bindVar x t >> return ()
  uni (TSyn c [] _) (TSyn c' [] _)
    | c == c'       = return ()
  uni (TSyn _ _ t1) t2  = unify t1 t2
  uni t1 (TSyn _ _ t2)  = unify t1 t2
  uni (TApp s1 s2) (TApp t1 t2) = unify s1 t1 >> unify s2 t2
  uni (TCon x) (TCon y)
    | x == y        = return ()
  uni s t           = err (TypeMismatch s t)


-- returns 'True' if we can make types the same by only binding vars in arg 1.
-- XXX: This has a bug...
-- suppose that we are matching:
-- (a,a)  against   (b,Int)
-- 1. pairs match
-- 2. a := b
-- 3. b := Int    -- wrong, we don't know that "b" is int

{-
match              :: Type -> Type -> TypeM Bool
match s t           = do s <- inBase (pruneIO False s)
                         t <- inBase (pruneIO False t)
                         uni s t
  where
  uni (TFree x) t               = bindVar x t >> return True
  uni (TSyn c [] _) (TSyn c' [] _)
    | c == c'                   = return True
  uni (TSyn _ _ t1) t2          = match t1 t2
  uni t1 (TSyn _ _ t2)          = match t1 t2
  uni (TApp s1 s2) (TApp t1 t2) = match s1 t1 `andM` match s2 t2
  uni (TCon x) (TCon y)
    | x == y                    = return True
  uni _ _                       = return False
-}



match              :: Type -> Type -> TypeM Bool
match t1 t2         = do xs <- inBase (fvs t2)
                         r <- try (unifyWith xs t1 t2)
                         return (case r of
                                   Left _  -> False
                                   Right _ -> True)


unifyWith          :: [TyVar] -> Type -> Type -> TypeM Bool
unifyWith xs s t    = withSkolems xs (unify' s t)

unify'             :: Type -> Type -> SolverM Bool
unify' s t          = do (x,y) <- unify2 s t
                         return (x || y)

-- Returns (vars bound on left, vars bound on right)
-- Note: in "improvemnt by instance" we assume that variables
-- on the left will get bound first.
unify2             :: Type -> Type -> SolverM (Bool,Bool)
unify2 s t          = do s <- inBase (pruneIO False s)
                         t <- inBase (pruneIO False t)
                         uni s t
  where
  uni (TFree x) t               = do b <- uniVar x t
                                     return (b,False)
  uni t (TFree x)               = do b <- uniVar x t
                                     return (False,b)
  uni (TSyn c [] _) (TSyn c' [] _) | c == c'
                                = return (False,False)
  uni (TSyn _ _ t1) t2          = unify2 t1 t2
  uni t1 (TSyn _ _ t2)          = unify2 t1 t2
  uni (TApp s1 s2) (TApp t1 t2) = do (xs1,ys1) <- unify2 s1 t1 
                                     (xs2,ys2) <- unify2 s2 t2
                                     return (xs1 || xs2, ys1 || ys2)
  uni (TCon x) (TCon y)
    | x == y        = return (False,False)
  uni s t           = err' (TypeMismatch s t)


isSko x             = do sko <- ask
                         return (x `elem` sko)

uniVar x t          = do b <- isSko x
                         if b then uniSko x t else lift (bindVar x t)

uniSko k t@(TFree x)  = do b <- isSko x
                           if b then if k == x 
                                        then return False
                                        else err' (BoundTypeVariable k t)
                                else lift (bindVar x (TFree k))
uniSko k (TSyn _ _ t) = uniSko k t
uniSko k t            = err' (BoundTypeVariable k t)

sameKind a b          = do k1 <- kindOf a
                           k2 <- kindOf b
                           same <- inBase (sameIO k1 k2)
                           when (not same) (err (KindMismatch k1 k2))

bindVar              :: TyVar -> Type -> TypeM Bool
bindVar x t           = do sameKind x t
                           b <- occursCheck x t
                           when b (inBase (setVar x t))
                           return b



-- Returns 'True' if we should bind the variable to the type,
-- 'False' otherwise (i.e. the type is really a type synonym for the
-- variable itself).  We raise an exception if unification would require
-- a recursive type.
occursCheck          :: TyVar -> Type -> TypeM Bool
occursCheck x t       = tSyns t 
  where
  tSyns (TFree y) | x == y  = return False
  tSyns (TSyn _ _ t)        = tSyns =<< inBase (pruneIO True t)
  tSyns t                   = occurs t >> return True

  occurs t            = occ =<< inBase (pruneIO True t)
  occ (TFree y)
    | x == y          = err (x `OccursIn` t)
  occ (TApp t1 t2)    = occurs t1 >> occurs t2
  occ _               = return ()
                  
 
class KindOf t where
  kindOf             :: t -> TypeM Kind

instance KindOf Type where
  kindOf (TApp t1 _)  = do k <- kindOf t1 
                           case k of
                             _ `TApp` _ `TApp` k -> return k
                             _ -> bug ("kindOf")
                                    (show t1 ++ " is not fun but, " ++ show k)
  kindOf (TFree x)    = kindOf x
  kindOf (TCon x)     = do Forall [] [] t <- lkpTCon x    
                           return t
  kindOf (TSyn _ _ t) = kindOf t
  kindOf (TInfix {})  = "kindOf" `unexpected` "TInfix"
  kindOf (TParens {}) = "kindOf" `unexpected` "TParens"
  
instance KindOf TyVar where
  kindOf (TyVar _ _ k)= return k
  kindOf (TyUser {})  = "kindOf" `unexpected` "TyUser"


 


