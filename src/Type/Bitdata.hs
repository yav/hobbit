-- | Additional processing for bitdata declarations.
--
-- This module assumes that the bitdata declarations:
--    (i)   have been kind checked, and 
--    (ii)  are provided in dependency order.
--
-- Axioms for bitdata declarations:
--  * BitRep            Convert to bit vector
--  * BitData           Convert from bit vector
--  * Field             Access field
--  * UpdFiled          Update field
--  * ValIn             Read/write memory
--  * SizeOf (LE/BE t)  Define memory area
--
-- We also perform analysis to detect junk and confusion.


module Type.Bitdata (checkBitdata) where

import AST
import Type.Monad 
import Type.Error
import Type.Algs
import qualified Type.Env
import qualified BDD
import Error
import qualified Pass

import Utils
import MonadLib hiding(collect)
import Data.Word
import Data.List(find,mapAccumL)

-- We use the typing monad for its ability to solve predicates.
-- Note: could we split the typing monad into multiple monads,
-- separating the inference and solving components?

-- | API to bitdata.
checkBitdata :: Type.Env.Env -> RuleEnv
             -> [BitData] -> Pass.Pass ([BDT],[Rule],[ExpBind])
checkBitdata primTs rEnv bs' 
  = do let bs = map hackBitdata bs'
       (r,ws) <- Type.Monad.run (emptyDB { typingEnv  = Type.Env.empty 
                                         , kindingEnv = primTs 
                                         , rules      = rEnv
                                         })
               $ loop [] bs
       Pass.warn ws
       return r
  where
  loop ws []        = do bs <- getBDTs
                         as <- getRules
                         return ( (reverse bs, as, ctrDecls =<< bdtCtrs =<< bs)
                                , ws)
  loop ws (f:fs)    = do (f,as',ws') <- flatData f
                         withBDT f 
                           $ withRules as'
                           $ loop (ws'++ws) fs



-- A quick and dirty way to support the alternative bitdata notation.
hackBitdata b         = b { bdCtrs = map hack2to1 (bdCtrs b) }

hack2to1           :: FlatCon -> FlatCon
hack2to1 f@(FlatCon {}) = f
hack2to1 f@(FlatCon2 c fs i)  = FlatCon c (l2Fields fs)
                                          (Just (toLay fs)) i
  where 
  toLay (BF_Named f)    = [LayField (fieldName f)]
  toLay BF_Wild         = [LayWild]
  toLay (BF_Tag n)      = [LayInt (fromIntegral n) Nothing]
  toLay BF_Unit         = []
  toLay (BF_Sig l t)    = [LaySig (toLay l) t]
  toLay (BF_Cat l r)    = toLay l ++ toLay r





--------------------------------------------------------------------------------
-- We turn defaults and 'if' clauses into ordinary definitions, so that
-- they can be processed uniformly in the following passes.  We relay on 
-- later passes to eliminate unused defaults.

ctrDecls c          = ifDecl c ++ 
                      concatMap (defaultDecl (bcName c)) (bcFields c)

-- Default value for a constructor
defaultDecl c f     = case fieldDefault f of
                        Nothing -> []
                        Just e  -> [ ExpBind (ImpBind x (MIs e)) t ]
                          where x   = defName c (fieldName f)
                                t   = mono (fieldType f)

-- 'if' clause test for a constructor
ifDecl c            = case bcIf c of
                        Nothing -> []
                        Just e  -> [ ExpBind (ImpBind x check) ty ]
                          where x   = ifCheckName (bcName c)
                                ty  = mono $ foldr tFun tBool 
                                           $ map fieldType fields
                                check   = foldr MPat (MIs e) args
                                args    = map (PVar . fieldName) fields
                                fields  = bcFields c
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Check one bitdata declaration.


compWidths :: BitData -> TypeM (Word32,Bool,BDT)
compWidths d  = 
  do ((ns,lss),gs) <- collect (unzip # forEach (bdCtrs d) conWidth)
     let inBD = cBitData `elem` bdDeriving d

     case ns of
  
         -- No constructors.
         []   -> return (0, inBD, BDT { bdtName   = bdName d,
                                        bdtCtrs   = [],
                                        bdtCover  = BDD.pWild 0 })

         -- We have constructors.
         n:ns -> do forEach ns (unify n)
                    gWidth <- newGoal (CIn cWidth [n])
                    solveGoals (gWidth : gs) []
                    lss <- forEach lss (\ls -> forEach ls staticLayout)
                    let ctrs  = zipWith newCon (bdCtrs d) lss 
                        cvr   = foldr1 BDD.pOr (map bcCover ctrs)
                    n' <- staticTNat n
                    return (n',inBD, BDT { bdtName  = bdName d,
                                           bdtCtrs  = ctrs,
                                           bdtCover = cvr })
                  


flatData          :: BitData -> TypeM (BDT, [Rule], [String])
flatData d = inDefn (bdName d) $
  do (n,inBD,bdt) <- compWidths d
     let warn1 = if inBD then reportJunk bdt else []
         overs = checkOverlaps (bdtCtrs bdt)
         warn2 = map (reportOverlap bdt) overs 

         bdTs = if inBD then bdtCtrs bdt
                        else concat $ [ [c1,c2] | (c1,c2,_) <- overs ]

     bd_goals <- bitdataFields bdTs
     solveGoals bd_goals []

     rs <- concat # forEach (bdtCtrs bdt) (ruleField (bdName d))
     let t  = bdtAsType bdt
         axes = (if inBD then [ ruleBitData n t ] else [])
                  ++ ruleBitRep n t : ruleMem n t ++ rs
     return (bdt,axes, warn1 ++ warn2)



bitdataFields overs = loop [] [] overs
  where
  loop done preds (c:cs) | bcName c `elem` done = loop done preds cs
  loop done preds (c:cs)  = do ps <- mapM (inBitData . fieldType) (bcFields c)
                               loop (bcName c : done) (ps++preds) cs
  loop _ preds [] = return preds
                        
  inBitData t = do n <- newTVarAnon kNat
                   newGoal (CIn cBitData [t,n])




-- Changes the constructor data structures.
newCon             :: FlatCon -> [(Layout,Word32)] -> BDTCtr
newCon c ls         = BDTCtr {
                        bcName    = fcName c,
                        bcFields  = fcFields c,
                        bcLayout  = toFreeLayout ls,
                        bcIf      = fcIf c,
                        bcCover   = covers ls
                      } 

-- | Convert a sequence of layout specs (with their widths),
-- into a context independent form:
-- Example: (1,3) # (x,4) # (0,2) becomes: (1@6:3), (x@2:4), (0@0:2)
-- XXX: I don't think the FreeLayout format is used for anything (check)
toFreeLayout       :: [(Layout,Word32)] -> [FreeLayout]
toFreeLayout ls     = snd (mapAccumL step 0 (reverse ls))
  where
  step o (l,n)      = (o+n, l :@: AST.BitField o n)
                                   

staticLayout       :: (Layout,Type) -> TypeM (Layout,Word32)
staticLayout (l,t)  = do n <- staticTNat t
                         return (l,n)

-- | Calculates the set of bit patterns that will match
-- the pattern for the corresponding constructor.
covers             :: [(Layout,Word32)] -> BDD.Pat
covers l            = foldr BDD.pSplit (BDD.pWild 0) (map computeBDD l)
  where
  computeBDD (LayWild,n)      = BDD.pWild n
  computeBDD (LayInt l _,n)   = BDD.pInt n l
  computeBDD (LayField {}, n) = BDD.pWild n
  computeBDD (LaySig {},_)    = "computeBDD" `unexpected` "LaySig"




--------------------------------------------------------------------------------
  



--------------------------------------------------------------------------------
-- Compute the width of a constructor
-- Note: We compute the widths as types of kind Nat.
-- In this way we can infer some widths by using statements like
-- "the width of this should be the same as the width of that".

-- | Compute the width of a constructor and its representation.
-- Each component of the representation is also annotated with its width.
conWidth :: FlatCon -> TypeM (Type, [(Layout,Type)])
conWidth con            = inDefn (fcName con) $ widths con (fcLayout con)

widths :: FlatCon -> [Layout] -> TypeM (Type, [(Layout,Type)])
widths con ls           = do (ns,lss) <- unzip # forEach ls (width con)
                             n        <- tSum ns
                             return (n, concat lss)

-- XXX: Replace to use BitRep instead of BitData
width :: FlatCon -> Layout -> TypeM (Type, [(Layout,Type)])
width _ LayWild         = one LayWild `fmap` newTVarAnon kNat

width _ (LayInt x w)    = do n <- case w of
                                    Nothing -> newTVarAnon kNat
                                    Just n  -> return (tNat n)
                             return (one (LayInt x Nothing) n)

width con (LayField x)  = do n <- newTVarAnon kNat
                             t <- typeOf con x
                             newEv (CIn cBitRep [t,n])
                             return (one (LayField x) n)

width con (LaySig ls t) = do (n,ls) <- widths con ls
                             unify t (tBit n) -- Note: could allow other types?
                             return (n, ls)

one l n                 = (n, [(l,n)])

typeOf           :: FlatCon -> Name -> TypeM Type
typeOf con x      = case find ((x==) . fieldName) (fcFields con) of
                      Just f  -> return (fieldType f)
                      Nothing -> err (x `UndefinedFieldOf` fcName con) 

-- | Add a list of types.  
-- 1. We use properties of addition to add as many
-- statically known sizes as possible (opt. to reduce # of goals to solve).
-- 2. Note that the resulting type is just a Nat, and may not satisfy Width.
tSum               :: [Type] -> TypeM Type
tSum ts             = adder 0 [] ts
  where
  adder s d (TCon (TNat n) : ts)  = adder (s+n) d ts
  adder s d (t             : ts)  = adder s (t:d) ts
  adder s []     []               = return (tNat s)
  adder 0 (d:ds) []               = foldM add d ds
  adder s ds     []               = foldM add (tNat s) ds

  add t1 t2         = do n <- newTVarAnon kNat
                         newEv (CIn cAdd [t1,t2,n])
                         return n 
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
ctrOverlap c1 c2      = let o = bcCover c1 `BDD.pAnd` bcCover c2
                        in if BDD.willAlwaysFail o 
                              then [] 
                              else [(c1,c2,o)]

checkOverlaps        :: [BDTCtr] -> [(BDTCtr,BDTCtr,BDD.Pat)]
checkOverlaps []      = []
checkOverlaps (c:cs)  = concatMap (ctrOverlap c) cs ++ checkOverlaps cs


warnMsg            :: String -> [String] -> String
warnMsg msg msgs    = unlines (msg : map ('\t':) msgs)

-- | Check if a bitdata declaration contains junk.
reportJunk         :: BDT -> [String]
reportJunk t        = if BDD.willAlwaysFail junk then [] else
                          [warnMsg ("The type " ++ show (bdtName t) 
                                ++ " contains junk:") (BDD.showPat junk)]
  where junk = BDD.pNot (bdtCover t)

reportOverlap t (c1,c2,xs)
  = warnMsg ("Constructors " ++ show (bcName c1)
           ++ " and " ++ show (bcName c2)
           ++ " of type " ++ show (bdtName t)
           ++ " overlap:") (BDD.showPat xs)
--------------------------------------------------------------------------------






--------------------------------------------------------------------------------
-- These are the rules that we generate for bitdata declarations.

-- XXX: perhaps we should qualify all these rules by the predicates
-- on the relevant fileds.

ruleBitData :: Word32 -> Type -> Rule
ruleBitData w t   = Rule (\_ -> IntEv w) $ mono $ CIn cBitData [t, tNat w]

ruleBitRep :: Word32 -> Type -> Rule
ruleBitRep w t  = Rule (\_ -> IntEv w) $ mono $ CIn cBitRep [t, tNat w]

-- For memory areas.  We only derive instances for bitdata 
-- that fits in a whole number of bytes.
ruleMem :: Word32 -> Type -> [Rule]
ruleMem w t = case w `divMod` 8 of  
                   (b,0) -> rValIn b ++ rSizeOf b
                   _     -> []
  where
  rValIn n    = [ Rule (\_ -> leEv (IntEv n)) $ mono $ CIn cValIn [tLE t, t]
                , Rule (\_ -> beEv (IntEv n)) $ mono $ CIn cValIn [tBE t, t] ]

  rSizeOf n   = [ Rule proof $ mono $ CIn cSizeOf [tLE t, tNat n]
                , Rule proof $ mono $ CIn cSizeOf [tBE t, tNat n] ]
    where proof _ = IntEv n

-- The field manipulation instances.
-- Also the BitRep instances for the constructor types.
ruleField :: Name -> BDTCtr -> TypeM [Rule]
ruleField b f       = do let w = bcWidth f
                         hasRules  <- forEach (bcFields f) (hasField w)
                         return (ruleBitRep w ty : concat hasRules)
  where
  ty                = bcSubType b f
  ls                = [ (x,p) | LayField x :@: p <- bcLayout f ]

  hasField w (Field x t _) 
    = case [ p | (x',p) <- ls, x' == x ] of
        [] -> err (x `FieldNotLaidOut` bcName f)
        [p]  -> 
          let how _ = bitFieldEv (IntEv w) (IntEv (bfOffset p)) 
                                           (IntEv (bfWidth p))
          in return [ Rule how (mono (CIn cField [tLab x,ty,t]))
                    , Rule how (mono (CIn cUpdField [tLab x,ty,t]))
                    ]
        _ -> err (x `RepeatedField` bcName f)
--------------------------------------------------------------------------------




 
