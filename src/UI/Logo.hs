module UI.Logo(logo) where

import UI.ANSI
 
hobbit              = [" _           _     _     _    "
                      ,"| |         | |   | |   (_)  _"
                      ,"| |__   ___ | |__ | |__  _ _| |_"
                      ,"|  _ \\ / _ \\|  _ \\|  _ \\| (_   _)"
                      ,"| | | | |_| | |_) ) |_) ) | | |_ "
                      ,"|_| |_|\\___/|____/|____/|_|  \\__)"
                      ]
              
hob                :: Int -> [String] -> String
hob n ls            = unlines
                        ( map (color 7)         (take 2 $ drop 0 ls)
                       ++ map (bold . color n)  (take 2 $ drop 2 ls)
                       ++ map (color n)         (take 2 $ drop 4 ls)
                        ) 

logo n              = hob n hobbit 
                   ++ "a higher order language with bits\n"

