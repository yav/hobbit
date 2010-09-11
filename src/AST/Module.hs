module AST.Module
  ( Module(..), ExpListEntry(..), EntSpec(..), SubSpec(..), Import(..)
  ) where

import AST.Type
import AST.Data
import AST.Expr
import qualified ModSys.AST as M
import ModSys.AST hiding (Module,modName,modExpList,modImports)

import PP


data Module         = Module
                    { modName     :: ModName
                    , modExpList  :: Maybe [ExpListEntry]
                    , modImports  :: [Import]
                    , modTypes    :: [DataDecl]
                    , modBinds    :: BindBlock
                    }


  

{- ... the rest is defined in ModSys.AST ... -}


-- Pretty printing -------------------------------------------------------------

instance Show Module where show x = prShow x
instance Pr Module where
  pr m  = fsep [ text "module" <+> text (modName m), nest 2 exp, text "where" ]
        $$ vcat (map pr (modImports m))
        $$ text " "
        $$ vcat (map pr (modTypes m))
        $$ text " "
        $$ pr (modBinds m)
    where exp = case modExpList m of
                  Nothing -> empty
                  Just xs -> parens (fsep (punctuate comma (map pr xs)))

instance Pr ExpListEntry where
  pr (EntExp e)     = pr e
  pr (ModuleExp m)  = text "module" <+> text m  

instance Pr j => Pr (EntSpec j) where
  pr (Ent j Nothing)  = pr j
  pr (Ent j (Just x)) = pr j <> parens (pr x)

instance Pr SubSpec where
  pr AllSubs          = text ".."
  pr (Subs xs)        = fsep (punctuate comma (map pr xs))

instance Pr Import where
  pr i  = text "import" <+> p (impQualified i) "qualified"
        <+> text (impSource i) <+> as <+> p (impHiding i) "hiding"
        <+> parens (fsep (punctuate comma (map pr (impList i))))
    where 
    p True d  = text d
    p False _ = empty
    as  | impSource i == impAs i  = empty
        | otherwise               = text "as" <+> text (impAs i)
