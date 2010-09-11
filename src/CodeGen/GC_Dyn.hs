-- | Code that is different for different programs.
module CodeGen.GC_Dyn where

import qualified AST as A
import AST.SIL hiding (Stmt(..))
import qualified AreaLayout as L
import Error
import HAsm hiding (M)
import CodeGen.Labels
import CodeGen.Monad
import CodeGen.Mach
import CmdArgs

import Utils
import Data.Bits
import Data.List(nub,elemIndex,sortBy, groupBy,partition)
import Data.Maybe (isJust)
import qualified Data.Map as Map

import Text.PrettyPrint.HughesPJ


-- | reg_base: top of the heap
-- | Pointer to new object in reg_A
alloc   :: Integer -> M [Instr]
alloc n  = do f <- frameDescr
              addScav f
              return [ -- Check for end of heap
                       Mov the_size (lab (l_scav f)) (Reg reg_A)
                     , Mov the_size (num 0)          (arr n reg_base)

                       -- Allocate
                     , Mov the_size (Reg reg_base)        (Reg reg_A)
                     , Add the_size (num (word_size * n)) (Reg reg_base) ]


-- These are called by the RTS -------------------------------------------------

c_stmt x    = x <> semi
c_call f xs = text f <> parens (hsep (punctuate comma xs))
c_arr f x   = text f <> brackets x
c_fun t f xs b  = text t <+> text f <> parens (fsep $ punctuate comma xs)
               <+> text "{" $$ nest 2 (vcat (map c_stmt b)) $$ text "}"

c_table t n xs = text t <+> text n <> text "[] ="
               $$ nest 2 (rows xs $$ text "};")
  where first_row x = text "{" <+> text x
        other_row x = comma <+> text x
        rows (x:xs) = first_row x $$ vcat (map other_row xs)
        rows []     = text "{"


scavGlobsC :: [String] -> Doc
scavGlobsC xs =
  decls $$
  text "// Scavange global variables" $$
  c_fun "void" l_scav_globs []
    [ l <+> text "=" <+> c_call l_copy [l] | l <- map text xs ]

  where decls = case xs of
                  [] -> empty
                  xs -> text "extern Word" <+>
                          fsep (punctuate comma (map decl xs)) <> semi
        decl x = text "*" <> text x

scavangeFunC :: Shape -> Doc
scavangeFunC x =
  c_fun "Word*" (l_scav x) [text "Word* base"] $
   [ c_arr "base" n <+> text "= (Word)"
                    <+> c_call l_copy [text "(Word*)" <> c_arr "base" n]
        | n <- map integer (obj_ptrs x) ] ++
   [ text "return base +" <+> integer (obj_size x) ]

-- Tables ---------------------------------------------------------------------

sizeOf c      = 1 + fromIntegral (length (A.acFields c))
ptrsOf c      = [ n | (n,A.TCon t) <- zip [1..] (A.acFields c), isPtr t ]

conInfo n c   = let c' = A.poly c
                in (A.acName c', ConI n Shape { obj_size = sizeOf c'
                                              , obj_ptrs = ptrsOf c'
                                              })
conInfos a    = zipWith conInfo [1,3..] (A.adtCtrs a)

copy_tableC cs  = c_table "Word" l_copy_table (map (show . obj_size) cs)
scav_tableC cs  = c_table "Scavenger" l_scav_table (map l_scav cs)

scavFunsC cs  = vcat $ punctuate (text "\n") $ map scavangeFunC cs

addGCTag ss c = case elemIndex (cShape c) ss of
                  Just n -> c { cTag = (fromIntegral n `shiftL` half)
                                    .|. cTag c }
                  Nothing -> bug "addGCTag" (show c)
  where half = fromIntegral (word_size_bits `div` 2)


-- | Generate information about the constructors, and gc tables
gcData :: [FunADT] -> [A.ADT] 
       -> (Doc, Map.Map ConName ConInfo, Map.Map A.Name ConInfo, [Shape])
gcData fs as  = ( text "// GC tables" $$
                  copy_tableC ss $$
                  scav_tableC ss
                , Map.fromList [ (x, addGCTag ss c) | (x,c) <- cs1 ]
                , Map.fromList [ (x, addGCTag ss c) | (x,c) <- cs2 ]
                , ss
                )
  where cs1  = concatMap conInfos fs
        cs2  = concatMap conInfos as
        ss   = nub ( Shape { obj_size = 0, obj_ptrs = [] }
                   : map (cShape . snd) cs1
                  ++ map (cShape . snd) cs2
                   )

-- Note: the first element in the table is a dummy, to enebale us to 
-- GC uninitizlied global variables.
-- All global variables are initizlied with a value that is a pointer to 0.
-- Then the GC tag is 0, and so the GC will use the first entry in
-- the tables to GC such objects. 



-- | Generate the map of global variables, and the code to declare them,
-- initialisze some of them, and the scavange_globals method.
gcGlobs :: [Option] -> [Decl] -> L ([Instr], Doc, Map.Map Name GlobVar)
gcGlobs opts ds = do (dsA,bs1) <- defineAreas opts areas 
                     xs <- forEach (concatMap vars ds) globVar
                     let (bs2,ds) = unzip xs 
                     return ( Section ".data"
                            : dsA         -- declare area
                           ++ concat ds   -- declare other globals
                            , scavGlobsC [ l | (_,GlobVar l True) <- bs2 ]
                            , Map.fromList (bs1 ++ bs2))
  where
  vars (AVal x _) = [x]
  vars (Cyc xs)   = [ x | (x,_,_) <- xs ]
  vars _          = []

  areas :: [Area]
  areas = [ L.Area (r, varName x) (cvtAlign a) (fromIntegral s) v
                | Area x r v (A.OpEv A.AreaEv [A.IntEv s, A.IntEv a]) <- ds ]

  cvtAlign a  = case lg2 (fromIntegral a) of
                  Just x -> word_size_bits - x
                  Nothing -> bug "cvtAlign" ("Bad alignment: " ++ show a)




globVar (Bind x t)  = do l <- newLabelL
                         let p = isPtr t
                             v = if p then Lab l_dummy else Num 0
                         return ( (x,GlobVar l p)
                                , [ Global l, Comment (show x),
                                     Label l, Init the_size [v]]
                                )

-- Ordering of areas ----------------------------------------------------------

type Area = L.Area (Maybe String, Name)   -- (region name, area name)

areaRange :: Area -> Maybe String
areaRange a = fst (L.name a)


defineAreas :: [Option] -> [Area] -> L ([Instr], [(Name,GlobVar)])
defineAreas opts as  
  = do (ds, gs) <- unzip # forEach groupAreas (orderRange getRange) 
       return (concat ds, concat gs)
  where
  -- Group areas by the region they occupy.
  groupAreas  = groupBy ((==) `on` areaRange) 
              $ sortBy (compare `on` areaRange) as

  -- find a region
  getRange  :: String -> L.Region
  getRange x  = case lookup x ranges of
                  Just r  -> r
                  Nothing -> error ("Unknown range: " ++ show x)

  -- The region map    
  ranges     :: [(String,L.Region)]
  ranges      = map pRange [ r | Range r <- opts ]

  -- parse a region specification
  pRange :: String -> (String, L.Region)
  pRange r = case parseRange r of
               Just (name,from,size) -> (name, (from, from + size - 1))
               Nothing -> error ("Invalid range: " ++ show r)



orderRange :: (String -> L.Region) -> [Area] 
            -> L ([Instr], [(Name,GlobVar)])
orderRange getRange as 
  = case areaRange (head as) of

      -- automatically allocated area
      Nothing -> do let (abs,oth) = partition (isJust . L.addr) as
                        as' = L.pack oth  -- order the area

                    -- define space for areas
                    (ls,decAs) <- unzip # forEach as' areaDef

                    -- define pointers for areas.
                    -- XXX: this is unnecessary:
                    -- use $L instead of using a separate pointer...
                    (decPs1,gs1) <- unzip # forEach2 ls as' ptrDefLab
  
                    -- define the pointers for user-defined areas
                    -- (these are the ones withe explicit '=')
                    (decPs2,gs2) <- unzip # forEach abs ptrDef
                    return ( concat decAs ++ concat decPs1 ++ concat decPs2 
                           , gs1 ++ gs2 )   

      -- user specified area  
      Just s -> do let reg = getRange s
                   case L.order reg as of
                     Just s  -> do (is,bs) <- unzip # forEach s ptrDef
                                   return (concat is, bs)
                     Nothing -> error ("Cannot fit areas in region " ++ s)


areaDef :: Area -> L (String, [Instr])
areaDef a = do l <- newLabelL
               let theAlign = max word_size (2^(word_size_bits - L.align a))
                   theSize  = fromIntegral (L.dwordSize a)
               return ( l
                      -- declare area
                      , [ Comment (show (snd (L.name a)))
                        , Align theAlign
                        , Label l
                        , Space theSize B1 ]
                      )


-- (Declare area, globvar)
ptrDefLab :: String -> Area -> L ([Instr], (Name, GlobVar))
ptrDefLab l a = do l1 <- newLabelL
                   let name = show (snd (L.name a))

                          -- declare pointer to an area
                   return ( [ Comment name
                            , Label l1
                            , Init the_size [Lab l] ]

                          , (snd (L.name a), GlobVar l1 False)
                          )
                  

ptrDef :: Area -> L ([Instr], (Name, GlobVar))
ptrDef area         = do l <- newLabelL
                         return ( [ Comment (show (L.name area))
                                  , Label l
                                  , Init word [val] ]
                                , (snd (L.name area), GlobVar l False)
                                )
  where 
  val = case L.addr area of
          Just x -> Num x 
          Nothing -> bug "ptrDef" ("Area " ++ show (L.name area) 
                                        ++ " not laied out.")
          
                        








