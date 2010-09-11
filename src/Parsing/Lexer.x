{ 
module Parsing.Lexer (Lexeme(..), Token(..), lexer, layout) where

import Error
import Parsing.Token
import Parsing.Range

import Data.Char(toLower)
}


$octDigit    = [0-7]
$decDigit    = [0-9]
$hexDigit    = [0-9A-Fa-f]
$symbol      = [\~ ! @ \# \$ \% \^ & \* \- \+ = \/ \\ \< \> \? \. : \|]

@binInt      = "B" [0-1]+
@kbInt       = $decDigit+ "K"
@mbInt       = $decDigit+ "M"
@gbInt       = $decDigit+ "G"
@octInt      = 0 [oO] $octDigit+
@decInt      = $decDigit+
@hexInt      = 0 [xX] $hexDigit+
@varId       = [a-z_][a-zA-Z_0-9]*\'*
@conId       = [A-Z][a-zA-Z_0-9]*
@varSym      = ($symbol # :) $symbol*
@conSym      = : $symbol*
@modName     = [A-Z][a-zA-Z_0-9]*        
             
:-


<0,comment>"{-"             { startComment }

<comment> {
"-}"                        { endComment }
.                           ;
\n                          ;
}

<string> {
[^\"]                       { addString }
\"                          { endString }
}



<0> {
$white+                     ;
"--" .*                     ;

-- Keywords --------------------------------------------------------------------
"area"                      { emit KW_Area }
"as"                        { emit KW_As }
"bitdata"                   { emit KW_Bitdata }
"case"                      { emit KW_Case }
"class"                     { emit KW_Class }
"data"                      { emit KW_Data }
"deriving"                  { emit KW_Deriving }
"do"                        { emit KW_Do }
"else"                      { emit KW_Else }
"if"                        { emit KW_If }
"import"                    { emit KW_Import }
"in"                        { emit KW_In }
"instance"                  { emit KW_Instance }
"let"                       { emit KW_Let }
"module"                    { emit KW_Module }
"of"                        { emit KW_Of }
"primitive"                 { emit KW_Primitive }
"struct"                    { emit KW_Struct }
"then"                      { emit KW_Then }
"type"                      { emit KW_Type }
"where"                     { emit KW_Where }


-- Reserved operators ----------------------------------------------------------
"."                         { emit Dot }
".."                        { emit DotDot }
"::"                        { emit DoubleColon }
"="                         { emit Equals }
"\"                         { emit Backslash }
"|"                         { emit Bar }
"<-"                        { emit LeftArrow }
"->"                        { emit RightArrow }
"=>"                        { emit FatRightArrow }
"~"                         { emit Tilde }
    
-- Symbols ---------------------------------------------------------------------
"("                         { emit LeftParen }
")"                         { emit RightParen }
";"                         { emit Semi }
"{"                         { emit LeftCurly }
"}"                         { emit RightCurly }
"["                         { emit LeftBracket }
"]"                         { emit RightBracket }
","                         { emit Comma }
"`"                         { emit BackQuote }
"'"                         { emit Quote }

-- Characters
'.'                         { emitS (CharTok . head . tail) }

-- Strings
\"                          { startString }

-- Numbers
@binInt        { emitS (\s -> let bits = tail s
                              in BinTok (cvt 2 (map fromBinDigit bits))
                                        (fromIntegral (length bits))) }
@octInt        { emitS (IntTok . cvt 8  . map fromOctDigit . drop 2) }
@hexInt        { emitS (IntTok . cvt 16 . map fromHexDigit . drop 2) }
@kbInt         { emitS (IntTok . (kb *) . cvt 10 . map fromDecDigit . init) }
@mbInt         { emitS (IntTok . (mb *) . cvt 10 . map fromDecDigit . init) }
@gbInt         { emitS (IntTok . (gb *) . cvt 10 . map fromDecDigit . init) }
@decInt        { emitS (IntTok . cvt 10 . map fromDecDigit) }


-- qualified names
@modName "." @varId         { emitS (qualName QVarId) }
@modName "." @conId         { emitS (qualName QConId) }
@modName "." @varSym        { emitS (qualName QVarSym) }
@modName "." @conSym        { emitS (qualName QConSym) }

-- unqualified names
@varId                      { emitS VarId }
@conId                      { emitS ConId }
"." @varId                  { emitS (LabId . tail) }
@varSym                     { emitS VarSym }
@conSym                     { emitS ConSym }
}


  
                     
{

-- Number conversion -----------------------------------------------------------
kb,mb,gb       :: Integer
kb              = 1024
mb              = 1024 * kb
gb              = 1024 * mb

cvt            :: Integer -> [Integer] -> Integer
cvt rad ds      = sum (zipWith (\n x -> rad^n * x) [0..] (reverse ds))

fromBinDigit   :: Char -> Integer
fromBinDigit    = fromDecDigit

fromOctDigit   :: Char -> Integer
fromOctDigit    = fromDecDigit

fromDecDigit   :: Char -> Integer
fromDecDigit x  = read [x]
  
fromHexDigit :: Char -> Integer
fromHexDigit x'
  | 'a' <= x && x <= 'f'  = fromIntegral (10 + fromEnum x - fromEnum 'a')
  | otherwise             = fromDecDigit x
  where x                 = toLower x'
--------------------------------------------------------------------------------

  
qualName f xs       = let (q,_:n) = break ('.'==) xs in f (q,n)


data Lexeme         = Lexeme { lexPos :: Range, lexTok :: Token }

instance Show Lexeme where show l = show (lexPos l, lexTok l)


-- | The different lexers (or the different state of the lexer).
data LexS           = Normal                      -- normal parsing
                    | InComment ![Position]       -- where comments start
                    | InString !Position !String  -- start; data

stateToInt Normal         = 0
stateToInt (InComment {}) = comment
stateToInt (InString {})  = string

data AlexInput      = Inp { alexPos           :: !Position,
                            alexInputPrevChar :: !Char,
                            input             :: !String 
                          }

alexGetChar        :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar i =
  case input i of
    c:cs  -> Just (c, Inp { alexPos = move (alexPos i) c,
                            alexInputPrevChar = c,
                            input = cs })
    []    -> Nothing

type Action = Position -> String -> LexS -> (Maybe Lexeme, LexS)


emit                           :: Token -> Action 
emit t p s z                    = (Just $ Lexeme (fromString p s) t,z)

emitS                          :: (String -> Token) -> Action 
emitS f p s z                   = (Just $ Lexeme (fromString p s) (f s),z)

startComment                   :: Action
startComment r _ Normal         = (Nothing, InComment [r])
startComment r _ (InComment cs) = (Nothing, InComment (r : cs))
startComment _ _ _              = bug "startComment" "Comment in string."
                         
endComment                     :: Action
endComment _ _ (InComment [_])    = (Nothing,Normal)
endComment _ _ (InComment (_:cs)) = (Nothing,InComment cs)
endComment _ _ _                  = bug "endComment" "End of comment."

startString                    :: Action 
startString r _ Normal          = (Nothing,InString r [])
startString _ _ _               = bug "startString" ""

addString                      :: Action 
addString _ c (InString p cs)   = (Nothing,InString p (c++cs))
addString _ _ _                 = bug "addString" ""

endString                      :: Action 
endString q _ (InString p cs) = (Just $ Lexeme (Range p q) (StrTok str), Normal)
  where str = reverse cs
endString _ _ _                 = bug "endString" ""


lexer      :: String -> [Lexeme]
lexer xs    = lex initInp Normal
  where
  initInp   = Inp { alexPos = start,
                    alexInputPrevChar = '\n',
                    input = xs }
  lex i s =
    case alexScan i (stateToInt s) of
      AlexEOF ->
        case s of
          Normal          -> []
          InString p _    -> [Lexeme (Range p end) UnterminatedString]
          InComment (p:_) -> [Lexeme (Range p end) UnterminatedComment]
          InComment _     -> bug "lexer.lex.EOF" ""
      AlexError i' -> [Lexeme (Range (alexPos i) (alexPos i')) LexicalError]
      AlexSkip i' _ -> lex i' s
      AlexToken i' l act -> 
        let txt       = take l (input i)
            (mtok,s') = act (alexPos i) txt s
            rest      = lex i' s'
        in case mtok of
             Nothing -> rest
             Just t  -> t : rest



-- Layout
--------------------------------------------------------------------------------
-- NOTE: This is different from Haskell's layout rule but
-- hopefully the same in "normal" cases.


data Block  = Block Token !Int

layout     :: [Block] -> [Lexeme] -> [Lexeme]

layout ctxt (l : ls) 
  | tok == KW_In  = close ctxt
  where
  pos         = lexPos l
  tok         = lexTok l
  curly       = Lexeme (fromPos (from pos)) RightCurly

  close (Block KW_Let _ : ctxt) = curly : l : layout ctxt ls
  close (_ : ctxt)              = curly : close ctxt
  close []                      = [Lexeme pos InWithoutLet]

layout sameCtxt@(Block _ block : newCtxt) sameLex@(l : ls) 
  | col > block   = emitL sameCtxt l ls 
  | col < block   = Lexeme pos RightCurly : layout newCtxt sameLex 
  | otherwise     = Lexeme pos Semi : l : layout sameCtxt ls  -- XXX: emit l?
  where 
  pos = lexPos l
  col = column (from pos)

layout [] (l : ls)  = emitL [] l ls

layout ctxt []      = [ Lexeme (fromPos end) RightCurly | _ <- ctxt ]


emitL ctxt l ls 
  | tok == KW_Where 
 || tok == KW_Of 
 || tok == KW_Let 
 || tok == KW_Do  = l : curly : next ls
  where
  pos         = lexPos l
  tok         = lexTok l
  curly       = Lexeme (fromPos (to pos)) LeftCurly

  next (l:ls) = l : layout (Block tok (column $ from $ lexPos l) : ctxt) ls
  next []     = layout (Block tok (column (to pos)) : ctxt) []
emitL ctxt l ls = l : layout ctxt ls



}


