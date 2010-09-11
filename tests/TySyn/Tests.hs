module Current.Tests where

import System

dir   = "TySyn"
tests = 
      [ (["1.bit"], ExitSuccess)
      , (["2.bit"], ExitFailure 1)
      , (["3.bit"], ExitFailure 1)
      , (["4.bit"], ExitFailure 1)
      , (["5.bit"], ExitFailure 1)
      , (["6.bit"], ExitSuccess)
      ]
     




