module PP (module PP, module Pretty) where

import Text.PrettyPrint.HughesPJ as Pretty hiding (TextDetails(..))

class Pr a where
    pr             :: a -> Doc
    pr x            = prn 0 x

    prn            :: Int -> a -> Doc
    prn _ x         = pr x


prShow            :: Pr a => a -> String
prShow x            = render (pr x)


vpr                :: [Doc] -> Doc
vpr []              = empty
vpr [x]             = x
vpr (x:xs)          = x $+$ text "" $+$ vpr xs

lineUp d1 d2 d3 (x:xs) = d1 <+> x 
                      $$ vcat [ d2 <+> x | x <- xs ]
                      $$ d3
lineUp d1 _ d3 []      = d1 <+> d3

prOpt Nothing _     = empty
prOpt (Just x) f    = f x

commaSep ds         = hsep (punctuate comma ds)

block              :: [Doc] -> Doc
block []            = braces empty
block [d]           = char '{' <+> d <+> char '}'
block (d:ds)        = vcat ( char '{' <+> d
                           : [ semi <+> d | d <- ds ]
                           ++ [ char '}' ])

cdot                = char '\xB7'
-- cdot                = char '*'
tris d              = char '\xAB' <> d <> char '\xBB'
-- tris d              = char '<' <> d <> char '>'


