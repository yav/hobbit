-- An example of using the Tree HTML utitlity.

import Tree
import System.Directory

test x y    = do t <- getDir x x
                 writeFile y (html [t])

-- example:
getDir d n  = do xs <- getDirectoryContents d
                 (ds,fs) <- split xs
                 cs <- mapM (\x -> getDir (d++"/"++x) x) ds
                 cs' <- mapM addPerms fs
                 let cs'' = [ Node [c] [] | c <- cs' ]
                 p <- getPermissions d
                 return (Node [n :? show p] (cs++cs''))
  where
  addPerms x  = do p <- getPermissions (d++"/"++x)
                   return (x :? show p)

  
  split (x:xs)
    | x == "." || x == ".."   = split xs
  split (x:xs)  = do b <- doesDirectoryExist (d ++ "/" ++ x)
                     (as,bs) <- split xs
                     return (if b then (x:as,bs) else (as,x:bs))
  split []      = return ([],[])


