module ModSys.Ents 
  ( Entity(..),owns,isCon         -- for module system (only need Entity type)
  , EntType(..), origName, isType -- for compiler
  ) where

import AST.Type
import qualified Data.Set as Set

-- interface of the module system to the concrete type of entities

data Entity         = Entity 
                    { definedIn :: ModName
                    , name      :: Name
                    , entType   :: EntType } deriving Eq

data EntType        = Value | Constr | Type (Set.Set Entity)

owns e              = case entType e of
                        Type cs -> cs
                        _       -> Set.empty

isCon e             = case entType e of
                        Constr -> True 
                        _      -> False

isType e            = case entType e of
                        Type _  -> True
                        _       -> False

instance Show EntType where
  show Value        = "V"
  show Constr       = "C"
  show (Type _)     = "T"

instance Eq EntType where
  x == y            = compare x y == EQ

instance Ord EntType where
  compare Value Value           = EQ
  compare Constr Constr         = EQ
  compare (Type _) (Type _)     = EQ

  compare Value _           = LT
  compare (Type _) _        = GT
  compare Constr y          = compare y Constr


instance Show Entity where
  show x            = show (origName x) -- ++ "(" ++ show (entType x) ++ ")"

instance Ord Entity where
  compare e1 e2     = case compare (definedIn e1) (definedIn e2) of
                        LT -> LT
                        EQ -> case compare (name e1) (name e2) of
                                LT -> LT
                                EQ -> compare (entType e1) (entType e2)
                                GT -> GT
                        GT -> GT

origName           :: Entity -> Name
origName e          = Qual (definedIn e) (name e)


