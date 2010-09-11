module Parsing.Token where

data Token   

-- Reserved identifiers

    = KW_Area | KW_As
    | KW_Bitdata
    | KW_Data | KW_Deriving | KW_Do
    | KW_Case | KW_Class
    | KW_Else   
    | KW_If | KW_Import | KW_In | KW_Instance
    | KW_Let      
    | KW_Module
    | KW_Of       
    | KW_Primitive
    | KW_Struct
    | KW_Then | KW_Type
    | KW_Where


-- Reserved operators

    | Dot
    | DotDot 
    | DoubleColon
    | Equals
    | Backslash
    | Bar
    | LeftArrow
    | RightArrow
    | FatRightArrow
    | Tilde


-- Symbols

    | LeftParen | RightParen
    | LeftCurly | RightCurly
    | LeftBracket | RightBracket
    | Semi
    | Comma 
    | BackQuote
    | Quote

    | QVarId (String,String)
    | QConId (String,String)
    | QVarSym (String,String)
    | QConSym (String,String)

    | VarId String
    | ConId String
    | LabId String
    | VarSym String
    | ConSym String

    | BinTok { value :: Integer, len :: Integer }    
    | IntTok Integer
    | CharTok Char 
    | StrTok String

-- Errors

    | UnterminatedComment 
    | UnterminatedString 
    | InWithoutLet
    | LexicalError
      deriving (Eq, Show)
