{
{-# OPTIONS_GHC  -W #-}
module Parsing.Parser (parseMod,parseExpr,parseRule) where

import Parsing.Lexer
import AST 
import Parsing.Utils
import Parsing.Range
import Utils(uncurry3)
}

%token


-- Reserved identifiers --------------------------------------------------------
     
        'area'          { Lexeme $$ KW_Area }
        'as'            { Lexeme $$ KW_As } 
        'bitdata'       { Lexeme $$ KW_Bitdata }
        'case'          { Lexeme $$ KW_Case }
        -- 'class'          { Lexeme $$ KW_Class }
        'data'          { Lexeme $$ KW_Data }
        'deriving'      { Lexeme $$ KW_Deriving }
        'do'            { Lexeme $$ KW_Do }
        'else'          { Lexeme $$ KW_Else }
        'if'            { Lexeme $$ KW_If }
        'import'        { Lexeme $$ KW_Import }
        'in'            { Lexeme $$ KW_In }
        -- 'instance'      { Lexeme $$ KW_Instance }
        'let'           { Lexeme $$ KW_Let }
        'module'        { Lexeme $$ KW_Module }
        'of'            { Lexeme $$ KW_Of }
        'primitive'     { Lexeme $$ KW_Primitive }
        'struct'        { Lexeme $$ KW_Struct }
        'then'          { Lexeme $$ KW_Then } 
        'type'          { Lexeme $$ KW_Type }
        'where'         { Lexeme $$ KW_Where }


-- Reserved operators ----------------------------------------------------------

        '::'            { Lexeme $$ DoubleColon }
        '='             { Lexeme $$ Equals }
        '|'             { Lexeme $$ Bar }
        '<-'            { Lexeme $$ LeftArrow }
        '->'            { Lexeme $$ RightArrow }
        '=>'            { Lexeme $$ FatRightArrow }
        '..'            { Lexeme $$ DotDot }
        '~'             { Lexeme $$ Tilde }
        '\\'            { Lexeme $$ Backslash }
        
-- Symbols ---------------------------------------------------------------------

        '('             { Lexeme $$ LeftParen }
        ')'             { Lexeme $$ RightParen }
        ';'             { Lexeme $$ Semi }
        '{'             { Lexeme $$ LeftCurly }
        '}'             { Lexeme $$ RightCurly }
        '['             { Lexeme $$ LeftBracket }
        ']'             { Lexeme $$ RightBracket }
        ','             { Lexeme $$ Comma }
        '`'             { Lexeme $$ BackQuote }
        '\''            { Lexeme $$ Quote }
        
        
-- Semi-reserved identifiers/operators -----------------------------------------

        'hiding'        { Lexeme $$ (VarId "hiding") }     -- import
        'qualified'     { Lexeme $$ (VarId "qualified") }  -- import
        'size'          { Lexeme $$ (VarId "size") }       -- struct
        '#'             { Lexeme $$ (VarSym "#") }         -- # pred, bitdata
        '+'             { Lexeme $$ (VarSym "+") }         -- + pred , n+k pat
        '*'             { Lexeme $$ (VarSym "*") }         -- * pred
        '^'             { Lexeme $$ (VarSym "^") }         -- 2^ pred
        '-'             { Lexeme $$ (VarSym "-") }         -- pred, n-k pat
        '_'             { Lexeme $$ (VarId "_") }


-- Other -----------------------------------------------------------------------

        QVARID          { Lexeme _ (QVarId $$) }
        QCONID          { Lexeme _ (QConId $$) }
        QVARSYM         { Lexeme _ (QVarSym $$) }
        QCONSYM         { Lexeme _ (QConSym $$) }

        VARID           { Lexeme _ (VarId $$) }
        CONID           { Lexeme _ (ConId $$) }
        LABID           { Lexeme _ (LabId $$) }
        VARSYM          { Lexeme _ (VarSym $$) }
        CONSYM          { Lexeme _ (ConSym $$) }

        BIN             { Lexeme _ $$@(BinTok {}) }
        INT             { Lexeme _ (IntTok $$) }
        STRING          { Lexeme _ (StrTok $$) }
        CHAR            { Lexeme _ (CharTok $$) }

    
        
%monad { ParseM } { (>>=) } { return }
%name parseMod module
%name parseExpr expr
%name parseRule rule
%tokentype { Lexeme } 

-- weaker
%left ','
%left '::'
-- stronger




%%


-- Modules ---------------------------------------------------------------------

module                       :: { Module }
  : 'module' modName 
    modExports 'where' 
   '{' modBody '}'              { uncurry3 (Module $2 $3) $6 }

modBody                      :: { ([Import],[DataDecl],BindBlock) }
  : imports semis topDecls      { ($1,fst $3, snd $3) }
  | imports                     { ($1,[],emptyBindBlock) }
  | topDecls                    { ([],fst $1, snd $1) }
  | {- empty -}                 { ([],[],emptyBindBlock) }

modExports                   :: { Maybe [ ExpListEntry ] }
  : '(' exports ')'             { Just $2 }
  | {- empty -}                 { Nothing }

imports                      :: { [Import] }
  : import                      { [$1] }
  | imports semis import        { $3 : $1 }

import                       :: { Import }
  : 'import' optQualified  modName optAsImp impList
                                { Import
                                { impQualified  = $2
                                , impSource     = $3
                                , impAs         = $4 $3
                                , impHiding     = fst $5
                                , impList       = snd $5 }}

optQualified                 :: { Bool }
  : 'qualified'                 { True }
  | {- empty -}                 { False }

optAsImp                     :: { ModName -> ModName }
  : 'as' modName                { \_ -> $2 }
  | {- empty -}                 { id } 

impList                      :: { (Bool,[EntSpec Name]) }
  : '(' entSpecs ')'            { (False, $2) }
  | 'hiding' '(' entSpecs ')'   { (True, $3) }
  | {- empty -}                 { (True, []) }
  
entSpecs                     :: { [EntSpec Name] }
  : {- empty -}                 { [] }
  | entSpec                     {% (: []) `fmap` impSpec $1 }    
  | entSpecs ',' entSpec        {% (: $1) `fmap` impSpec $3 }

exports                      :: { [ ExpListEntry ] }
  : {- empty -}                 { [] }
  | export                      { [$1] }
  | exports ',' export          { $3 : $1 }

export                       :: { ExpListEntry }
  : 'module' modName            { ModuleExp $2 }
  | entSpec                     { EntExp $1 }

entSpec                      :: { EntSpec QName }
  : tyConUse optSubSpec         { Ent (Q $1) $2 }
  | varUse                      { Ent (Q $1) Nothing }

optSubSpec                   :: { Maybe SubSpec }
  : {- empty -}                 { Nothing }
  | '(' '..' ')'                { Just AllSubs }
  | '(' subs ')'                { Just (Subs $2) } 

subs                         :: { [Name] }
  : {- empty -}                 { [] }
  | name                        { [$1] }
  | subs ',' name               { $3 : $1 }



-- Top Declarations ------------------------------------------------------------

topDecls                     :: { ([DataDecl], BindBlock) }
  : topDecls1                   {% topDecls $1 }

topDecls1                    :: { [ParseTop] }
  : topDecl                     { [$1] }
  | topDecls1 semis topDecl     { $3 : $1 }

topDecl                      :: { ParseTop }
  : bind                        { TopBind $1 }
  | typeDecl                    { TopType $1 }


typeDecl                     :: { DataDecl }
  : 'bitdata' tyConDef '=' flatCons  optDeriving    
    { BitdataDecl $ BitData $2 (reverse $4) $5 }   

  | 'data' tyConDef tyParams '=' dataCons   
    { DataDecl $ AlgData $2 (reverse $3) (reverse $5) }

  | 'type' tyConDef tyParams '=' type      
    { TypeDecl $ TypeSyn $2 (reverse $3) $5 }

  -- XXX: some notation for preds
  | 'struct' tyConDef tyParams optSize 'where' fieldBlock 
    { StructDecl $ Struct { stName   = $2
                          , stParams = reverse $3
                          , stFields = mono $6 
                          , stSize   = $4 
                          } }

  | 'primitive' tyConDef '::' type 
    { KSigDecl (KSig $2 $4) }

    

tyParam                      :: { TParam }
  : tyVar                       { TP $1 Nothing }

tyParams                     :: { [TParam] }
  : {- empty -}                 { [] }
  | tyParams tyParam            { $2 : $1 } 

optDeriving                  :: { [Name] }
  : 'deriving' tyConUse           { [$2] }
  | 'deriving' '(' tyConUses ')'  { reverse $3 }
  | {- empty -}                   { [] }

tyConUses                    :: { [Name] }
  : tyConUse                    { [$1] }
  | tyConUses ',' tyConUse      { $3 : $1 }

dataCons                     :: { [DataCon] }
  : dataCon                     { [$1] }
  | dataCons '|' dataCon        { $3 : $1 }

dataCon                      :: { DataCon }
  : type                        {% typeToCon $1 }

flatCons                     :: { [FlatCon] }
  : flatCons '|' flatCon        { $3 : $1 }
  | flatCon                     { [$1] }

flatCon                      :: { FlatCon } 
  : conDef optFields optAs optIf { FlatCon $1 $2 $3 $4 }
  | conDef field2 optIf        { FlatCon2 $1 $2 $3 }

field2s                      :: { Layout2 }
  :                             { BF_Unit }
  | field2                      { $1 }
  | field2s '|' field2          { BF_Cat $1 $3 }

field2                       :: { Layout2 }
  : field                       { BF_Named $1 }
  | '_'                         { BF_Wild }
  | INT                         { BF_Tag (fromIntegral $1) }
  | BIN                         { BF_Tag (fromIntegral (value $1)) 
                                  `BF_Sig` TApp (prelType "Bit") 
                                                (tNat $ fromIntegral $ len $1) }
  | '[' field2s ']'             { $2 }
  | field2 '::' type            { BF_Sig $1 $3 }


optFields                    :: { [ Field ] }
  : {- empty -}                 { [] }
  | '{' fields '}'              { reverse $2 }

fields                       :: { [Field] }
  : fields ',' field            { $3 : $1 }          
  | field                       { [$1] }

field                        :: { Field }
  : label optDefault '::' type  { Field $1 $4 $2 }

optDefault                   :: { Maybe Expr }
  : '=' infExpr                 { Just $2 }
  | {- nothing -}               { Nothing } 

optAs                        :: { Maybe [Layout] }
  : {- nothing -}               { Nothing }
  | 'as' layout                 { Just (reverse $2) }

optIf                        :: { Maybe Expr }
  : {- nothing -}               { Nothing }
  | 'if' expr                   { Just $2 }                                    

layout                       :: { [Layout] }
  : layout '#' layAtom          { $3 ++ $1 }
  | layout '::' type            { [LaySig (reverse $1) $3] }
  | layAtom                     { $1 }

layAtom                      :: { [Layout] }
  : label                       { [LayField $1] }
  | '_'                         { [LayWild] }
  | INT                         { [LayInt (fromIntegral $1) Nothing] }
  | BIN                         { [LayInt (fromIntegral (value $1))
                                       (Just (fromIntegral (len $1)))] }
  | '(' layout ')'              { $2 }


optSize                       :: { Maybe Type }
  : {- empty -}                 { Nothing }
  | '|' 'size' type             { Just $3 }

fieldBlock                   :: { [StructField] }
  : '{' struct_fields '}'       { reverse $2 } 

struct_fields                :: { [StructField] }
  : struct_field                    { [$1] }
  | struct_fields ';' struct_field  { $3 : $1 }

struct_field                 :: { StructField }
  : label '::' type             { StField $1 $3 False }
  | '..' label '::' type        { StField $2 $4 True }
  | '..'                        { StPad Nothing }
  | type                        { StPad (Just $1) }


-- Expressions -----------------------------------------------------------------

expr                         :: { Expr }
  : infExpr '::' type           { Sig $1 $3 }
  | 'let' bindBlock 'in' expr   { Match (MGrd $2 (MIs $4)) }
  | 'case' expr 'of' '{' caseAlts '}' { eCase $2 $5 }
  | 'if' expr 'then' expr 
              'else' expr       { eIf $2 $4 $6 }
  | '\\' aPats '->' expr        { Match (foldr MPat (MIs $4) (reverse $2)) }
  | 'do' '{' stmts '}'          { $3 }
  | infExpr                     { $1 }

infExpr                      :: { Expr }
  : apExpr op expr              { Infix $1 $2 $3 }
  | apExpr                      { $1 }

apExpr                       :: { Expr }
  : apExpr atomExpr             { $1 `App` $2 }
  | atomExpr                    { $1 }

atomExpr                     :: { Expr }
  : '(' expr ')'                { Parens $2 }
  | '(' commaExprs ')'          { apps (Var (Tup (fromIntegral (length $2))) )
                                                                (reverse $2) }
  -- | atomExpr '.' label          { Var (Select $3) `App` $1 }
  -- | '(' '.' label ')'           { Var (Select $3) }
  | atomExpr LABID              { Var (Select (VarName $2)) `App` $1 }
  | '(' LABID ')'               { Var (Select (VarName $2)) }
  | name                        { Var $1 } 
  | name '{' recFields '}'      { eRecord $1 $3 }
  | name '{' '}'                { eRecord $1 [] }
  | INT                         { intLit $1 }
  | BIN                         { binLit $1 }
  | CHAR                        { charLit $1 }
  | STRING                      { strLit $1 }

commaExprs                   :: { [Expr] }
  : expr ',' expr               { [$3,$1] }
  | commaExprs ',' expr         { $3 : $1 }

recFields                    :: { [FieldV] }
  : recFields ',' recField      { $3 : $1 }
  | recField                    { [$1] }

recField                     :: { FieldV } 
  : label '=' expr              { FieldV $1 Nothing $3 }

caseAlt                      :: { Expr -> Match } 
  : pat rhsArr                  { \e -> MGrd (QPat $1 e) $2 }

caseAlts                     :: { Expr -> Match } 
  : caseAlt                     { $1 }
  | caseAlts ';' caseAlt        { \e -> $1 e `MOr` $3 e }


-- XXX: allow signatures?
stmts                        :: { Expr }
  : varDef '<-' expr ';' stmts  { Do (PVar $1) $3 $5 }
  | varDef '::' type '<-' expr ';' stmts  { Do (PVar $1 `PSig` $3) $5 $7 }
  | expr ';' stmts              { Do PWild $1 $3 }
  | 'let' bindBlock ';' stmts   { Match (MGrd $2 (MIs $4)) }
  | expr                        { $1 }



-- Patterns --------------------------------------------------------------------

pat                          :: { Pat }
  : conUse aPats                { pCon $1 (reverse $2) }
  | pat '::' typeApp            { PSig $1 $3 }
  | pat conopUse aPat           { PInfix $1 $2 $3 }    
  | pat '#' aPat                { pSplit $1 $3 }
  | pat '+' apExpr              { pIxUpd Dec $3 (Var (VarName "minIx")) $1 }
  | pat '-' apExpr              { pIxUpd Inc $3 (Var (VarName "maxIx")) $1 }
  | aPat                        { $1 }

aPat                         :: { Pat }
  : '(' pat ')'                 { PParens $2 }
  | '(' pat '|' qual ')'        { PAbs $2 $4 }
  | '(' commaPats ')'           { pCon (Tup (fromIntegral (length $2)))
                                                              (reverse $2) }
  -- | '(' varDef '+' INT '|' expr ')' {% pDecBd $2 $4 $6 }
  -- | '(' varDef '-' INT '|' expr ')' {% pIncBd $2 $4 $6 }
  | '{' patFields '}'           { pFields PWild (reverse $2) }
  | '{' pat '|' patFields '}'   { pFields $2 (reverse $4) }
  | '{' '}'                     { PWild }
  | '_'                         { PWild }
  | varDef                      { PVar $1 }
  | varDef 'as' aPat            { pAs $1 $3 }
  | conUse                      { pCon $1 [] }
  | INT                         { pInt $1 }
  | BIN                         { pBin $1 }
  | CHAR                        { pChar $1 }
  -- | STRING                      { pStr $1 }

commaPats                    :: { [Pat] }
  : pat ',' pat                 { [$3,$1] }
  | commaPats ',' pat           { $3 : $1 }

patFields                    :: { [FieldP] }
  : patFields ',' patField      { $3 : $1 }
  | patField                    { [$1] }

patField                     :: { FieldP }
  : label '=' pat               { FieldP $1 Nothing $3 }

aPats                        :: { [Pat] }
  : aPats aPat                  { $2 : $1 }
  | aPat                        { [$1] }

-- Bindings --------------------------------------------------------------------

-- XXX: If a binding (and hance a block of bindings) can start with a pattern
-- we have a problem, because  when we see '{' we don't know if it is the
-- beginning of a record pattern, or starting explicit layout.

-- Solution: The real problem here is that the parser has to guess
-- if the programmer wants to use explicit or implicit layout so we need
-- some way to indicate which should be used.
-- One way to solve this is to specify at the module level if this module
-- uses explict or implict layout (for the whole module).  This grammer
-- is written for the explicit layout.  A pass between the lexer and the
-- parser can conevrt implicit into explicit layout if desired.



bindBlock                    :: { Qual }
  : '{' binds '}'               {% fmap QLet (bindBlock $2) }
  | '{' '}'                     { QLet emptyBindBlock }

binds                        :: { [ParseBind] }
  : bind                        { [$1] }
  | binds semis bind            { $3 : $1 }

bind                         :: { ParseBind }
  : prim                        { ParsePrim $1 }
  | area                        { ParseArea $1 }
  | sig                         { ParseSig (fst $1) (snd $1) }
  | varDef rhs                  { ParseBind $ ImpBind $1 $2 }
  | varDef aPats rhs            { ParseBind $ ImpBind $1 $ foldr MPat $3 
                                                         $ reverse $2 }

sig                          :: { (Name,Schema) }
  : varDef '::' schema          { ($1,$3) }
  -- | '(' '~' ')' '::' schema     { (VarName "~",$5) }  -- XXX: hmm

prim                         :: { PrimDecl }
  : 'primitive' sig             { PrimDecl (fst $2) Nothing (snd $2) }

area                         :: { AreaDecl }
  : 'area' varDef optVal optRegion '::' type { AreaDecl $2 $4 $3 Nothing $6 }
  


optRegion                    :: { Maybe String }
  : {- empty -}                 { Nothing }
  | 'in' STRING                 { Just $2 }

optVal                       :: { Maybe Integer }
  : '=' INT                     { Just $2 }
  | {- empty -}                 { Nothing }

rhs                          :: { Match }
  : '=' expr                    { MIs $2 }
  | guards                      { $1 }
  | rhs 'where' bindBlock       { MGrd $3 $1 }

guards                       :: { Match }
  : guards guard                { MOr $1 $2 }
  | guard                       { $1 }

guard                        :: { Match }
  : '|' qual '=' expr           { MGrd $2 (MIs $4) }


rhsArr                       :: { Match }
  : '->' expr                   { MIs $2 }
  | guardsArr                   { $1 }
  | rhsArr 'where' bindBlock    { MGrd $3 $1 }
 
guardsArr                    :: { Match }
  : guardsArr guardArr          { MOr $1 $2 }
  | guardArr                    { $1 }

guardArr                     :: { Match }
  : '|' qual '->' expr          { MGrd $2 (MIs $4) }

qual                         :: { Qual }
  : 'if' expr                   { QGrd $2 }
  | pat '<-' expr               { QPat $1 $3 }
  | qual ',' qual               { QThen $1 $3 }


-- Types ---------------------------------------------------------------------


schema                       :: { Schema }
  : type '=>' type              {% typeToSchema $1 $3 }
  | type                        { mono $1 }

rule                         :: { Poly Pred }
  : schema                      {% schemaToRule $1 }

type                         :: { Type }
  : typeApp tyConopUse type     { TInfix $1 $2 $3 }
  | typeApp                     { $1 } 

  -- Predicates:
  | typeApp '#' typeApp '=' typeApp { prelType ":#" `TApp` $1 `TApp` $3 `TApp` $5 }
  | typeApp '+' typeApp '=' typeApp { prelType ":+" `TApp` $1 `TApp` $3 `TApp` $5 }
  | typeApp '-' typeApp '=' typeApp { prelType ":+" `TApp` $5 `TApp` $3 `TApp` $1 }
  | typeApp '*' typeApp '=' typeApp { prelType ":*" `TApp` $1 `TApp` $3 `TApp` $5 }
  | typeApp '^' typeApp '=' typeApp {% tExp2 $1 $3 $5 }
  | '|' type '|' '=' atype      { TCon cBitRep `TApp` $2 `TApp` $5 }

typeApp                      :: { Type }
  : typeApp atype               { TApp $1 $2 }
  | atype                       { $1 }

atype                        :: { Type }
  : '(' type ')'                { TParens $2 }
  | '(' commaTypes ')'          { tTup (reverse $2) } 
  | tyConUse                    { TCon $1 }
  | tyConUse '\'' tyConDef      { tSub $1 $3 }
  | INT                         { tNat (fromIntegral $1) }
  | '(' label '::' ')'          { TCon (TLab $2) }
  | tyVar                       { tyVar $1 } 

commaTypes                   :: { [Type] }
  : type ',' type               { [$3,$1] }
  | commaTypes ',' type         { $3 : $1 }

commas                       :: { Integer }
  : ','                         { 1 }
  | commas ','                  { $1 + 1 } 



-- Identifiers -----------------------------------------------------------------

modName                      :: { ModName }
  : CONID                       { $1 }

varsym                       :: { String } 
  : VARSYM                      { $1 }
  | '+'                         { "+" }
  | '^'                         { "^" }
  | '*'                         { "*" }
  | '-'                         { "-" }
  | '#'                         { "#" } 

varid                        :: { String }
  : VARID                       { $1 }
  | 'hiding'                    { "hiding" }
  | 'size'                      { "size" }
  | 'qualified'                 { "qualified" }

varDef                       :: { Name }
  : varid                       { VarName $1 }
  | '(' varsym ')'              { VarName $2 }
  | '~'                         { VarName "~" }

varUse                       :: { Name }
  : varDef                      { $1 }
  | QVARID                      { qualName VarName $1 }
  | '(' QVARSYM ')'             { qualName VarName $2 }

varopDef                     :: { Name }
  : varsym                      { VarName $1 }
  | '`' varid '`'               { VarName $2 }

varopUse                     :: { Name }
  : varopDef                    { $1 }
  | QVARSYM                     { qualName VarName $1 }
  | '`' QVARID '`'              { qualName VarName $2 } 

conDef                       :: { Name }
  : CONID                       { ConName $1 }
  | '(' CONSYM ')'              { ConName $2 }
  | '(' ')'                     { Tup 0 }
  | '(' commas ')'              { Tup ($2+1) }
  
conUse                       :: { Name }
  : conDef                      { $1 }
  | QCONID                      { qualName ConName $1 }
  | '(' QCONSYM ')'             { qualName ConName $2 }

conopDef                     :: { Name }
  : CONSYM                      { ConName $1 }
  | '`' CONID '`'               { ConName $2 }

conopUse                     :: { Name }
  : conopDef                    { $1 }
  | QCONSYM                     { qualName ConName $1 }
  | '`' QCONID '`'              { qualName ConName $2 }

name                         :: { Name }
  : varUse                      { $1 } 
  | conUse                      { $1 }

op                           :: { Name }
  : varopUse                    { $1 }
  | conopUse                    { $1 } 

tyVar                        :: { Name } 
  : varid                       { VarName $1 }

tyConDef                     :: { Name }
  : conDef                      { $1 }
  | '(' '->' ')'                { ConName "->" }

tyConUse                     :: { Name }
  : conUse                      { $1 } 
  | LABID                       { TLab (VarName $1) }

tyConopUse                   :: { Name }
  : conopUse                    { $1 }
  | '->'                        { ConName "->" }

label                        :: { Name }
  : varid                       { VarName $1 }


semis                        :: { () }
  : ';'                         { () }
  | semis ';'                   { () }


