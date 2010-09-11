module Tree(Tree(..), Label(..), Forest, html) where

data Label  = String :? String    deriving Show
data Tree   = Node [Label] Forest deriving Show
type Forest = [Tree]

open  = "[+]"
close = "[-]"

label (txt :? "")   = txt
label (txt :? tip)  = "<span title=" ++ show tip ++ ">" ++ txt ++ "</span>"



tree_btn n  = " <a href='javascript:toggle(" ++ show n ++ ")' id=" 
                  ++ show ("ctrl" ++ n) ++ ">" ++ open ++ "</a> "


labels xs   = unwords (map label xs)

toggle      = [ "function toggle(x) {",
                "  b = document.getElementById('ctrl' + x).firstChild;",
                "  s = document.getElementById(x).style;",
                "  if (s.display == 'none') {",
                "    s.display = 'block';",
                "    b.nodeValue = " ++ show close ++ ";",
                "  } else {",
                "    s.display = 'none';",
                "    b.nodeValue = " ++ show open ++ ";",
                "  } }" ]

style       = [ "body { font-family: monospace }",
                "ul { display: none;",
                "     list-style: none;",
                "     border-left: thin solid;",
                "   }",
                " a { font-family: monospace;",
                "     text-decoration: none;",
                "     margin-left: -1em;",
                "   }"
              ]

dHead       = "<head>" : 
              "<script type='text/javascript'>" : toggle ++ "</script>" : 
              "<style type='text/css'>" : style ++ "</style>" :
              "</head>" : [] 

html :: Forest -> String
html t = unlines doc
  where
  doc = "<html>" : 
        dHead ++ 
        "<body>" :
        forest "0" t ++
        "<script type='text/javascript'>" :
        "document.getElementById('0').style.display='block'" :
        "</script>" :
        "</body>" : 
        "</html>" : []


tree :: String -> Tree -> [String]
tree n (Node ls ys) = let cs = forest n ys 
                          btn = case cs of
                                  [] -> ""
                                  _ -> tree_btn n
                      in ("<li>" ++ btn ++ labels ls) : cs
        
forest :: String -> Forest -> [String]
forest _ []   = []
forest n xs   = list $ zipWith bullet [0..] xs
  where 
  list xs     = ("<ul id=" ++ show n ++ ">") : concat xs ++ ["</ul>"]
  bullet x y  = tree (show x ++ "_" ++ n) y



