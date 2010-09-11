module Parser (anExpr, aModule, aRule, parse) where

import qualified Parsing.Utils as P
import qualified Parsing.Parser as P
import Pass

anExpr              = P.parseExpr
aModule             = P.parseMod
aRule               = P.parseRule

parse p txt         = case P.run txt p of
                        Left e   -> err [e]
                        Right a  -> return a






