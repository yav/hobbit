module UI.ANSI where

import Opts

cmd x
  | ansi_color  = "\27[" ++ show x ++ "m"
  | otherwise   = ""
  
bold x    = cmd 1 ++ x ++ cmd 22
color n x = cmd (30 + n) ++ x ++ cmd 39

[black,red,green,yellow,blue,magenta,cyan,white] = map color [0..7]

