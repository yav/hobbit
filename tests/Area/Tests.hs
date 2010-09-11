module Current.Tests where

import System

dir   = "Area"
tests = 
      [ (["1.bit"], ExitSuccess)
      , (["2.bit"], ExitFailure 1)
      , (["3.bit"], ExitFailure 1)
      , (["4.bit"], ExitSuccess)
      , (["5.bit"], ExitSuccess)
      , (["6.bit"], ExitSuccess)
      , (["7.bit"], ExitSuccess)
      , (["8.bit"], ExitFailure 1)
      ]
     




