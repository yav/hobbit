-- | This module is used by the module system to manipulate names.
module ModSys.Names 
  (Name(..), QName, ModName
  , getQualifier, getQualified
  , mkUnqual, mkQual
  ) where


import AST.Type


getQualifier (Q (Qual q _)) = Just q
getQualifier _              = Nothing

getQualified (Q (Qual _ n)) = n
getQualified (Q n)          = n

mkUnqual x  = Q x
mkQual q x  = Q (Qual q x)


