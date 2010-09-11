module CmdArgs (cmdOptions, Option(..), Phase (..), parseRange) where

import System
import System.Console.GetOpt 


data Option  
  = InPath FilePath
  | OutFile FilePath
  | JustTypes (Maybe String)
  | Range String
  | Dump Phase (Maybe String)
  | Stop Phase
    deriving Eq

data Phase  = ModSys | Kinds | Bitdatas | Structs | Types 
            | Spec | SIL | CheckDefs | CC 
            deriving (Eq,Show,Enum)

dumpOpts = [ Option [] ["dump-" ++ show p] (OptArg (Dump p) "file")
             ("Dump result of phase `" ++ show p ++ "`") 
                | p <- [Structs,Spec,SIL,CC] ]
                


options
  = [ Option ['p'] ["path"] (ReqArg InPath "path") 
                            "Add `path' to module search path."
    , Option ['o'] ["out"] (ReqArg OutFile "file") 
                            "Write output to 'file.s' and 'file'."
    , Option ['t'] ["types"] (OptArg JustTypes "name")
                            "Just type check, and show type for 'name'"
    , Option ['r'] ["range"] (ReqArg Range "range=start:size")
                            "Address range for areas."
    ] ++ dumpOpts



parseRange :: String -> Maybe (String, Integer, Integer)
parseRange r  = case break ('='==) r of
                  (r@(_:_), _:xs) -> 
                    case break (':'==) xs of
                      (xs,_:ys) -> 
                         case (reads xs, reads ys) of
                           ([(x,"")],[(y,"")]) -> Just (r,x,y)
                           _ -> Nothing
                      _ -> Nothing
                  _ -> Nothing



cmdOptions :: IO ([Option],[String])
cmdOptions  = do as <- getArgs
                 case getOpt Permute options as of
                   (opts,xs,[]) -> return (opts,xs)
                   (_,_,errs)   -> do mapM putStrLn errs
                                      putStrLn (usageInfo msg options)
                                      exitFailure
  where msg = "hc [opts] <output> {modules}"






