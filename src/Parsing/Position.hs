module Parsing.Position where

import PP

data Position = Pos { chars :: !Int, row :: !Int, column :: !Int }
              | EOF
                deriving (Eq,Ord)
  
start                :: Position
start                 = Pos { chars = 0, row = 1, column = 1 } 

end                  :: Position
end                   = EOF

-- XXX: windows files? 
-- Perhaps handle in a scanner pass.
-- There we could also expand tabs and add a missing new line at eof
move :: Position -> Char -> Position
move (Pos a l c) '\t' = Pos (a+1)  l     (((c+7) `div` 8)*8+1)
move (Pos a l _) '\n' = Pos (a+1) (l+1)  1
move (Pos a l c) _    = Pos (a+1)  l     (c+1)
move EOF _            = EOF

instance Show Position where
  show EOF                           = "EOF"
  show (Pos { row = r, column = c }) = show r ++ ":" ++ show c

instance Pr Position where pr = text . show



