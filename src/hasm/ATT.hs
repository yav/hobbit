{-# LANGUAGE FlexibleInstances, GADTs #-}

-- | This module renders AT&T style assembly.
module ATT where

import Text.PrettyPrint.HughesPJ hiding(Style)
import HAsm


class ATT t where
  att :: t -> Doc


-- Operands --------------------------------------------------------------------

instance ATT (Reg t s) where
  att r       = char '%' <> text (show r)

instance ATT (Imm t s) where
  att i       = char '$' <> text (show i)

instance ATT (Mem t s) where
  att (Deref x)                   = parens (att x)
  att (Offset d Nothing Nothing)  = text (show d)
  att (Offset d (Just b) Nothing) = text (show d) <> parens (att b)
  att (Offset d b (Just (i,s)))
    = text (show d) <> parens (base <> comma <> att i <> comma <> scale)
    where base = case b of
                   Nothing -> empty
                   Just b  -> att b
          scale = text (show (bytes s))


instance ATT (Arg t s) where
  att (Reg r)     = att r
  att (Imm i)     = att i
  att (Mem m)     = att m



-- Instructions ----------------------------------------------------------------

instance ATT Instr where
  att (Add s a b) = att2 "add" s a b
  att (Sub s a b) = att2 "sub" s a b
  att (Mul s a)   = att1 "mul" s a
  att (Div s a)   = att1 "div" s a

  att (Inc s a)   = att1 "inc" s a
  att (Dec s a)   = att1 "dec" s a
  att (Neg s a)   = att1 "neg" s a

  att (And s a b) = att2 "and" s a b
  att (Or  s a b) = att2 "or"  s a b
  att (Xor s a b) = att2 "xor" s a b
  att (Not s a)   = att1 "not" s a 

  att (Shl s a b) = case a of
                      Nothing -> att2 "shl" s (Reg CL)  b
                      Just i  -> att2 "shl" s i  b
  att (Shr s a b) = case a of
                      Nothing -> att2 "shr" s (Reg CL)  b
                      Just i  -> att2 "shr" s i  b


  att (Bswap s a)   = att1 "bswap" s a

  att (Cmp s a b)   = att2 "cmp" s a b
  att (Test s a b)  = att2 "test" s a b
  att (Bt s a b)    = att2 "bt" s a b
  att (Btc s a b)   = att2 "btc" s a b
  att (Btr s a b)   = att2 "btr" s a b
  att (Bts s a b)   = att2 "bts" s a b

  att (Mov s a b)   = att2 "mov" s a b
  att (Xchg s a b)  = att2 "xchg" s a b
  att (Lea a b)     = text "lea" <+> att a <> comma <+> att b

  att (RepMovs s)   = att0 "rep movs" s
  att (RepStos s)   = att0 "rep stos" s

  att (Jmp a)     = text "jmp" <+> attJmp a
  att (JmpFar (FarImm seg off)) = text "ljmp" <+> att seg <> comma <+> att off
  att (JmpFar (FarMem a))       = text "ljmp" <+> attJmp a
  att (Call a)    = text "call" <+> attJmp a
  att (Ret Nothing)   = text "ret"
  att (Ret (Just x))  = text "ret" <+> att x

  att (J c i)     = text ("j" ++ show c) <+> attJmp i

  att (Push s a)  = att1 "push" s a
  att (Pop s a)   = att1 "pop" s a
  att Pusha       = text "pusha"
  att Popa        = text "popa"

  att Nop         = text "nop"

  att Clc         = text "clc"
  att Cld         = text "cld"
  att Cli         = text "cli"
  att Stc         = text "stc"
  att Std         = text "std"
  att Sti         = text "sti"

  att (In s Nothing)    = att2 "in" s (Reg DX) (regA s)
  att (In s (Just x))   = att2 "in" s x (regA s)

  att (Out s Nothing)  = att2 "out" s (regA s) (Reg DX) 
  att (Out s (Just x)) = att2 "out" s (regA s) x

  att Iret              = text "iret"

  att (Lgdt x)    = text "lgdt" <+> att x
  att (Lidt x)    = text "lidt" <+> att x
  att (Lldt x)    = text "lldt" <+> att x
  att (Ltr x)     = text "ltr" <+> att x

  att (Sgdt x)    = text "sgdt" <+> att x
  att (Sidt x)    = text "sidt" <+> att x
  att (Sldt x)    = text "sldt" <+> att x

  att (Invlpg x)  = text "invlpg" <+> att x
  att Halt        = text "hlt"

  -- Data
  att (Align x)   = text ".align" <+> text (show x)
  att (Space x n) = text ".space" <+> text (show (x * bytes n)) 
  att (Init u xs) = text dir <+> ds
    where ds      = commaSep (map (text . show) xs)
          dir    :: String
          dir     = case u of
                      B1 -> ".byte"
                      B2 -> ".word"
                      B4 -> ".dword"
                      B8 -> ".quad"
  att (String s)  = text ".string" <+> text (show s)

  -- Other
  att (Section x) = blank $$ (text ".section" <+> text x) $$ blank
  att (Label l)   = text l <> colon
  att (Global l)  = text ".global" <+> text l
  att (Comment l) = blank $$ char '#' <+> text l
  att (CommentBlock ls) = vcat ( blank
                               : text (replicate 60 '#')
                               : txtLine ""
                               : map txtLine ls
                            ++ [ txtLine ""
                               , text (replicate 60 '#')
                               , blank ])
    where
    txtLine x = char '#' <+> text x

regA   :: Size s -> Reg R s
regA B1 = AL
regA B2 = AX
regA B4 = EAX
regA B8 = RAX


att0 i s      = text (i ++ suffix s)
att1 i s a    = text (i ++ suffix s) <+> att a
att2 i s a b  = text (i ++ suffix s) <+> att a <> comma <+> att b

suffix      :: Size s -> String
suffix B1     = "b"
suffix B2     = "w"
suffix B4     = "l"
suffix B8     = "q"

attJmp (Reg r)          = char '*' <> att r
attJmp (Imm i)          = text (show i)
attJmp (Mem s)          = char '*' <> att s


instance ATT [Instr] where
  att is = foldr ($$) empty [ fieldOf i (att i) | i <- is ]


fieldOf (Label {}) x        = x
fieldOf (Comment {}) x      = x
fieldOf (CommentBlock {}) x = x
fieldOf _ x                 = nest 10 x

commaSep xs     = hsep (punctuate comma xs)
blank = text " "

