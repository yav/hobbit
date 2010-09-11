module Current.Tests where

import System

dir   = "Sig"
tests = 
      [ (["1.bit"], ExitSuccess)
      , (["2.bit"], ExitFailure 1)
      , (["3.bit"], ExitFailure 1)
      , (["4.bit"], ExitSuccess)
      , (["5.bit"], ExitSuccess)
      ]
     




