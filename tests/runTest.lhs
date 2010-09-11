#!/usr/local/bin/runhaskell

> import Current.Tests
> import System
> import System.Time

> type Test     = ([FilePath], ExitCode)
> hc            = "../src/hc -"

> main          = do xs <- mapM runTest tests
>                    let problems = [ fs | ((fs,_),False) <- zip tests xs ]
>                        logFile  = dir ++ "/" ++ "log"
>                    t <- getClockTime
>                    appendFile logFile $ unlines 
>                      ([ line, show t ] ++ map show problems ++ [ line ])

> line          = replicate 80 '-' 

> runTest      :: Test -> IO Bool
> runTest (mods,result) = (result ==) `fmap` system cmd
>   where cmd = unwords (hc : [ dir ++ "/" ++ f | f <- mods ])




