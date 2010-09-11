module Type.Error where

import AST
import PPIO
import PP

import Data.List(intersperse)
import Utils

data Error          = Err [Name] [ErrorT]

data ErrorT         = TyVar `OccursIn` Type
                    | RecursiveBitdata [Name]
                    | RecursiveTypeSynonyms [Name]
                    | Name `UndefinedFieldOf` Name
                    | UndefinedVariable Name
                    | UndefinedConstructor Name
                    | UndefinedTypeVariable TyVar
                    | UndefinedTypeConstructor Name
                    | TypeMismatch Type Type
                    | KindMismatch Kind Kind
                    | CannotSolve [TyVar] [Pred] [Pred]
                    | AmbiguousPredicate Pred
                    | AmbiguousStruct Name
                    | CannotGeneralize [TyVar]
                    | BoundTypeVariable TyVar Type
                    | Name `UninitializedFieldOf` Name
                    | Name `MultipleInitializers` Name
                    | Name `FieldNotLaidOut` Name
                    | Name `RepeatedField` Name
                    | TypeSynonymNotFullyApplied Name Int
                    | InvalidPredicate Type
                    | MiscError String
                      deriving Show

printError (Err xs es) 
  = do ds <- forEach es printErrorT
       return $ text "In" <+> hcat (intersperse (char '/') 
                                    $ reverse $ map pr xs) <> colon
             $$ nest 2 (vpr ds)

printErrorT :: ErrorT -> IO Doc
printErrorT e 
  = case e of

      a `OccursIn` t -> 
        do t <- printM t
           return (text "Recursive type:" $$
                   nest 2 (pr a <+> text "=" <+> t))

      RecursiveBitdata xs -> 
        return (text "Recursive 'bitdata' declarations:" $$ 
                nest 2 (commaSep (map pr xs)))

      RecursiveTypeSynonyms xs ->
        return (text "Recursive 'type' declarations:" $$
                nest 2 (commaSep (map pr xs)))

      x `UndefinedFieldOf` c ->
        return (text "Undefined field:" $$
                nest 2 (text "Constructor:" <+> pr c $$
                        text "Field:" <+> pr x))

      UndefinedVariable x ->
        return (text "Undefined variable:" <+> pr x)

      UndefinedConstructor x -> 
        return (text "Undefined constructor:" <+> pr x)

      UndefinedTypeVariable x -> 
        return (text "Undefined type variable:" <+> pr x)

      UndefinedTypeConstructor x -> 
        return (text "Undefined type constructor:" <+> pr x)

      TypeMismatch t1 t2 ->
        do t1 <- printM t1
           t2 <- printM t2
           return (text "Types differ:" $$ nest 2 (t1 $$ t2))

      KindMismatch k1 k2 -> 
        do k1 <- printM k1
           k2 <- printM k2
           return (text "Kinds differ:" $$ nest 2 (k1 $$ k2))

      CannotSolve xs ps qs ->
        runPrM $ withQuants xs $ \_ -> 
          do xs <- map snd # getQuants
             let xs' = case xs of
                        [] -> empty
                        xs -> text "Quantifiers:" <+> commaSep (map text xs)
             ps <- case ps of
                     [] -> return empty
                     ps -> do ps <- prM ps
                              return (text "Assumptions:" <+> ps)
             qs <- vcat # forEach qs prM
             return (text "Cannot discharge predicates:" $$
                       nest 2 (xs' $$ ps $$ text "Predicates:" <+> qs)) 

      AmbiguousPredicate p ->
        do p <- printM p
           return (text "Ambiguous predicate:" $$ nest 2 p)

      AmbiguousStruct x ->
        return (text "Struct" <+> text (show x) 
                              <+> text "does not have a well defined width.")

      CannotGeneralize xs ->
        return (text "Cannot generalize variables:" $$  
                  nest 2 (commaSep (map pr xs)))

      BoundTypeVariable x t ->
        do t <- printM t
           return (text "Type variable is not polymorphic:" $$
                      nest 2 (pr x <+> text "=" <+> t))

      x `UninitializedFieldOf` c -> 
        return (text "Uninitialized field:" $$
                nest 2 (text "Constructor:" <+> pr c $$
                        text "Field:" <+> pr x))

      x `MultipleInitializers` c ->
        return (text "Field initialized multiple times:" $$
                nest 2 (text "Constructor:" <+> pr c $$
                        text "Field:" <+> pr x))
      x `FieldNotLaidOut` c ->
        return (text "Field not present in 'as' clasue:" $$
                nest 2 (text "Constructor:" <+> pr c $$
                        text "Field:" <+> pr x))
      x `RepeatedField` c ->
        return (text "Repeated field:" $$
                nest 2 (text "Constructor:" <+> pr c $$
                        text "Field:" <+> pr x))



      TypeSynonymNotFullyApplied c n -> 
        return (text "Type synonym" <+> pr c <+> 
                text "needs" <+> int n <+> text "more arguments.")

      InvalidPredicate t ->
        do t <- printM t
           return (text "Invalid predicate:" <+> t)


      MiscError x -> return (text x)              







      






  

