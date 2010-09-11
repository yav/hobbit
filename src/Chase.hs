module Chase (chaseModules) where

import AST
import Parser
import Parsing.Fixity

import System.Directory(doesFileExist)
import System(getEnv)
import Data.List(find, isSuffixOf)
import Pass
import Utils


fileOpts ps x = [ path ++ "/" ++ fileName | path <- ps ]
  where
  fileName  | ".bit" `isSuffixOf` x  = x
            | otherwise              = x ++ ".bit"

modFile :: [FilePath] -> String -> Pass FilePath
modFile ps m = loop (fileOpts ps m) 
  where 
  loop (x:xs)  = do b <- io (doesFileExist x )
                    if b then return x else loop xs
  loop [] = err ["Cannot find module '" ++ m ++ "'"]
     

parseFile :: FilePath -> Pass Module
parseFile f = do msg ("Parsing " ++ show f)
                 rewrite =<< parse aModule =<< io (readFile f)

chaseModules :: [FilePath] -> [ModName] -> Pass [Module]
chaseModules ps ms = do qs <- io getPath
                        let path = concatMap splitPath ps ++ qs
                        loop path [] ms
  where
  loop _ done []  = return done
  loop ps done (m:ms)  
    = case find ((m ==) . modName) done of
        Just _  -> loop ps done ms
        Nothing -> do m <- parseFile =<< modFile ps m
                      loop ps (m:done) (map impSource (modImports m) ++ ms)


getPath :: IO [FilePath]
getPath = (splitPath # getEnv "BitPath") `catch` \_ -> return ["."]

splitPath xs  = case break (':' ==) xs of
                  (a, ':' : b) -> a : splitPath b
                  (a, "")      -> [a] 
                  _ -> error "getPath Impossible"


