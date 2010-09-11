#!/usr/local/bin/runhaskell

> import System(getArgs,system)
> import System.Directory(doesFileExist)
> import System.Exit(exitFailure)
> import Monad(when)
>
> main = do as <- getArgs
>           mapM_ runTest as
>
> runTest a = do x <- doesFileExist "Current"
>                when x $ do putStrLn "File 'Current' exists, quitting."
>                            exitFailure
>                system ("ln -s " ++ a ++ " Current")
>                system "./runTest.lhs"
>                system "rm Current"

