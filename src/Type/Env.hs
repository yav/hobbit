module Type.Env 
  ( Env
  , empty, ext, Type.Env.lookup, fromList, fromFun
  ) where

import AST
import Type.FVS
import qualified Data.Map as Map
import Control.Monad(mplus)

empty              :: Env
ext                :: (Name,Schema) -> Env -> Env
lookup             :: Name -> Env -> Maybe Schema
fromList           :: [(Name,Schema)] -> Env
fromFun            :: (Name -> Maybe Schema) -> Env

data Env            = Env (Map.Map Name Schema) (Name -> Maybe Schema)

empty               = Env Map.empty (const Nothing)
ext (x,s) (Env e f) = Env (Map.insert x s e) f
lookup x (Env a f)  = Map.lookup x a `mplus` f x
fromList xs         = Env (Map.fromList xs) (const Nothing)
fromFun f           = Env Map.empty f

-- Note: we assume that there are no free variables in the
-- function part of the environment.
instance FVS Env where
  fvs (Env e _ )    = fvs (Map.elems e)

instance Show Env where
  show (Env m _)    = show m






