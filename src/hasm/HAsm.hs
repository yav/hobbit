{-# LANGUAGE GADTs, ExistentialQuantification, EmptyDataDecls,
             MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances
  #-}

-- | This module desribes the assembly language.
module HAsm where

-- | Operand size types
data B1
data B2
data B4
data B8

-- | Operand sizes (in bytes)
data Size a where
  B1 :: Size B1
  B2 :: Size B2
  B4 :: Size B4
  B8 :: Size B8

type AddrSize = B8         -- ^ The size of addresses

addr :: Size AddrSize
addr = B8


-- | Convert a size to an integer.
bytes :: Size a -> Integer
bytes B1  = 1
bytes B2  = 2
bytes B4  = 4
bytes B8  = 8


-- | Operand types
data M                        -- ^ Memory
data R                        -- ^ General register
data SegR                     -- ^ Segment register
data CtrR                     -- ^ Control register
data I                        -- ^ Immediate 


-- | Condition codes
data Cond = O  | NO            -- ^ overflow 
          | C  | NC            -- ^ carry
          | S  | NS            -- ^ sign
          | P  | NP            -- ^ parity
          | E  | NE            -- ^ equal
          | L  | NL            -- ^ less then (signed)
          | LE | NLE           -- ^ less then or equal to (signed)
          | G  | NG            -- ^ greater then (signed)
          | GE | NGE           -- ^ greater then or equal to (signed)
          | B  | NB            -- ^ bellow (unsigned)
          | BE | NBE           -- ^ bellow or equal to (unsigned)
          | A  | NA            -- ^ above (unsigned)
          | AE | NAE           -- ^ above or equal to (unsigned)
            deriving Show

-- | Registers
data Reg t s where
  AL  :: Reg R B1
  BL  :: Reg R B1
  CL  :: Reg R B1
  DL  :: Reg R B1

  AH  :: Reg R B1
  BH  :: Reg R B1
  CH  :: Reg R B1
  DH  :: Reg R B1

  AX  :: Reg R B2
  BX  :: Reg R B2
  CX  :: Reg R B2
  DX  :: Reg R B2

  SP  :: Reg R B2
  BP  :: Reg R B2
  SI  :: Reg R B2
  DI  :: Reg R B2

  EAX :: Reg R B4
  EBX :: Reg R B4
  ECX :: Reg R B4
  EDX :: Reg R B4

  ESP :: Reg R B4
  EBP :: Reg R B4
  ESI :: Reg R B4
  EDI :: Reg R B4

  RAX :: Reg R B8
  RBX :: Reg R B8
  RCX :: Reg R B8
  RDX :: Reg R B8

  RSP :: Reg R B8
  RBP :: Reg R B8
  RSI :: Reg R B8
  RDI :: Reg R B8

  R8  :: Reg R B8
  R9  :: Reg R B8
  R10 :: Reg R B8
  R11 :: Reg R B8
  R12 :: Reg R B8
  R13 :: Reg R B8
  R14 :: Reg R B8
  R15 :: Reg R B8

  CS  :: Reg SegR B2
  DS  :: Reg SegR B2
  SS  :: Reg SegR B2
  ES  :: Reg SegR B2
  FS  :: Reg SegR B2
  GS  :: Reg SegR B2

  CR0 :: Reg CtrR B4
  CR1 :: Reg CtrR B4
  CR2 :: Reg CtrR B4
  CR3 :: Reg CtrR B4


data Mem t s where
  Deref  :: Reg R AddrSize -> Mem M s
  Offset :: Imm I AddrSize -> Maybe (Reg R AddrSize)
                           -> Maybe (Reg R AddrSize,Size x) -> Mem M s

data Imm t s where
  Lab :: String  -> Imm I AddrSize
  Num :: Integer -> Imm I s

data Arg t s = Reg (Reg t s) | Mem (Mem t s) | Imm (Imm t s)



data Instr

  -- Arithmetic
  = forall t1 t2 s. Arith2 t1 t2  => Add (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Arith2 t1 t2  => Sub (Size s) (Arg t1 s) (Arg t2 s)
  | forall t s.     Arith1 t      => Mul (Size s) (Arg t s)
  | forall t s.     Arith1 t      => Div (Size s) (Arg t s)

  | forall t s.     Arith1 t      => Inc (Size s) (Arg t s)
  | forall t s.     Arith1 t      => Dec (Size s) (Arg t s)
  | forall t s.     Arith1 t      => Neg (Size s) (Arg t s)

  -- Bits
  | forall t1 t2 s. Arith2 t1 t2  => And (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Arith2 t1 t2  => Or  (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Arith2 t1 t2  => Xor (Size s) (Arg t1 s) (Arg t2 s)
  | forall t s.     Arith1 t      => Not (Size s) (Arg t s)

  | forall t s.     Arith1 t      => Shl (Size s) (Maybe (Arg I B1)) (Arg t s)
  | forall t s.     Arith1 t      => Shr (Size s) (Maybe (Arg I B1)) (Arg t s)

  | forall s.       BSwap s       => Bswap (Size s) (Arg R s)

  -- Decisions
  | forall t1 t2 s. Cmp t1 t2     => Cmp  (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Cmp t1 t2     => Test (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Bt t1 t2      => Bt   (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Bt t1 t2      => Btc  (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Bt t1 t2      => Btr  (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Bt t1 t2      => Bts  (Size s) (Arg t1 s) (Arg t2 s)


  -- Moving
  | forall t1 t2 s. Mov  t1 t2    => Mov (Size s) (Arg t1 s) (Arg t2 s)
  | forall t1 t2 s. Xchg t1 t2    => Xchg (Size s) (Arg t1 s) (Arg t2 s)
  |                                  Lea (Arg M AddrSize) (Arg R AddrSize)

  -- Repeated
  | forall s.                        RepMovs (Size s)
  | forall s.                        RepStos (Size s)


  -- Jumps
  | forall t. JmpCall t           => Jmp (Arg t AddrSize)
  | forall t. JmpCall t           => Call (Arg t AddrSize)
  |                                  JmpFar FarOp
  |                                  Ret (Maybe (Arg I B2))

  | forall s.                        J Cond (Arg I s)

  -- Stack
  | forall t s.                      Push (Size s) (Arg t s)
  | forall t s. Pop t             => Pop  (Size s) (Arg t s)
  |                                  Pusha
  |                                  Popa

  -- Misc
  |                                  Nop

  -- Flags
  |                                  Clc | Cld | Cli
  |                                  Stc | Std | Sti
  -- Protected
  | forall s.                        In  (Size s) (Maybe (Arg I B1))
  | forall s.                        Out (Size s) (Maybe (Arg I B1))
  |                                  Iret

  |                                  Lgdt (Arg M AddrSize)
  |                                  Lidt (Arg M AddrSize)
  | forall t. Arith1 t            => Lldt (Arg t B2)
  | forall t. Arith1 t            => Ltr (Arg t B2)

  |                                  Sgdt (Arg M AddrSize)
  |                                  Sidt (Arg M AddrSize)
  | forall t. Arith1 t            => Sldt (Arg t B2)

  |                                  Invlpg (Arg M AddrSize)
  |                                  Halt

  -- Data
  |                                  Align Integer            -- ^ in bytes
  | forall x.                        Space Integer (Size x)
  | forall x.                        Init (Size x) [Imm I x]
  |                                  String String 

  -- Other
  |                                  Section String
  |                                  Label String
  |                                  Global String
  |                                  Comment String
  |                                  CommentBlock [String]


data FarOp                  = FarImm (Arg I B2) (Arg I B4)
                            | forall t. FarMem (Arg M t)



-- Restrictions on the argumnets of instructions -------------------------------

class Arith1 a
instance Arith1 R
instance Arith1 M

class Arith2 a b
instance Arith2 R R
instance Arith2 M R
instance Arith2 R M
instance Arith2 I R
instance Arith2 I M

class Bt a b
instance Bt R R
instance Bt R M
instance Bt I R
instance Bt I M

class JmpCall a
instance JmpCall R
instance JmpCall M
instance JmpCall I

class Pop a
instance Pop R
instance Pop SegR
instance Pop M

class Cmp a b
instance Cmp R R
instance Cmp M R
instance Cmp R M
instance Cmp I R
instance Cmp I M

class Xchg a b
instance Xchg R R
instance Xchg R M
instance Xchg M R

class BSwap t
instance BSwap B4
instance BSwap B8

class Mov a b
instance Mov R R
instance Mov M R
instance Mov R M
instance Mov I R
instance Mov I M
instance Mov SegR R
instance Mov SegR M
instance Mov R SegR
instance Mov M SegR -- except CS
instance Mov CtrR R
instance Mov R CtrR



--------------------------------------------------------------------------------

instance Show (Reg t s) where
  show AL   = "al"
  show BL   = "bl"
  show CL   = "cl"
  show DL   = "dl"

  show AH   = "ah"
  show BH   = "bh"
  show CH   = "ch"
  show DH   = "dh"

  show AX   = "ax"
  show BX   = "bx"
  show CX   = "cx"
  show DX   = "dx"

  show SP   = "sp"
  show BP   = "bp"
  show SI   = "si"
  show DI   = "di"

  show EAX  = "eax"
  show EBX  = "ebx"
  show ECX  = "ecx"
  show EDX  = "edx"

  show ESP  = "esp"
  show EBP  = "ebp"
  show ESI  = "esi"
  show EDI  = "edi"

  show RAX  = "rax"
  show RBX  = "rbx"
  show RCX  = "rcx"
  show RDX  = "rdx"

  show RSP  = "rsp"
  show RBP  = "rbp"
  show RSI  = "rsi"
  show RDI  = "rdi"

  show R8  = "r8"
  show R9  = "r9"
  show R10 = "r10"
  show R11 = "r11"
  show R12 = "r12"
  show R13 = "r13"
  show R14 = "r14"
  show R15 = "r15"

  show CS   = "cs"
  show DS   = "ds"
  show SS   = "ss"
  show ES   = "es"
  show FS   = "fs"
  show GS   = "gs"

  show CR0  = "cr0"
  show CR1  = "cr1"
  show CR2  = "cr2"
  show CR3  = "cr3"


instance Show (Imm t s) where
  show (Num x)  = show x
  show (Lab x)  = x


--------------------------------------------------------------------------------
-- Some sugar for operands

-- | A label immediate operand
lab :: String -> Arg I AddrSize
lab l = Imm (Lab l)

-- | A numeric immediate operrand
num :: Integer -> Arg I s
num n = Imm (Num n)



-- | Provides various ways to write memory operands
class MemSyn t where
  mem :: t -> Arg M s

-- disp
instance MemSyn (Imm I AddrSize) where
  mem i = Mem (Offset i Nothing Nothing)

-- disp
instance MemSyn Integer where
  mem i = mem (Num i :: Imm I AddrSize)

-- disp
instance MemSyn String where
  mem i = mem (Lab i)

-- base
instance MemSyn (Reg R AddrSize) where
  mem r = Mem (Deref r)

-- ix * scale
instance MemSyn (Reg R AddrSize, Size s) where
  mem (r,s) = mem (Num 0 :: Imm I AddrSize,r,s)

-- base + ix
instance MemSyn (Reg R AddrSize,Reg R AddrSize) where
  mem (r1,r2) = mem (r1,r2,B1)

-- base + ix * scale
instance MemSyn (Reg R AddrSize, Reg R AddrSize, Size s) where
  mem (r1,r2,s) = mem (Num 0 :: Imm I AddrSize,r1,r2,s)

-- disp + base
instance MemSyn (Imm I AddrSize, Reg R AddrSize) where
  mem (i,r) = Mem (Offset i (Just r) Nothing)

-- disp + base
instance MemSyn (Integer, Reg R AddrSize) where
  mem (i,r) = mem (Num i :: Imm I AddrSize,r)

-- disp + base
instance MemSyn (String, Reg R AddrSize) where
  mem (i,r) = mem (Lab i,r)

-- disp + ix * scale
instance MemSyn (Imm I AddrSize, Reg R AddrSize, Size s) where
  mem (i,r,s) = Mem (Offset i Nothing (Just (r,s)))

-- disp + ix * scale
instance MemSyn (Integer, Reg R AddrSize, Size s) where
  mem (i,r,s) = mem (Num i :: Imm I AddrSize,r,s)

-- disp + ix * scale
instance MemSyn (String, Reg R AddrSize, Size s) where
  mem (i,r,s) = mem (Lab i,r,s)

-- disp + base + ix
instance MemSyn (Imm I AddrSize, Reg R AddrSize, Reg R AddrSize) where
  mem (i,r1,r2) = mem (i,r1,r2,B1)

-- disp + base + ix
instance MemSyn (Integer, Reg R AddrSize, Reg R AddrSize) where
  mem (i,r1,r2) = mem (Num i :: Imm I AddrSize,r1,r2)

-- disp + base + ix
instance MemSyn (String, Reg R AddrSize, Reg R AddrSize) where
  mem (i,r1,r2) = mem (Lab i,r1,r2,B1)

-- disp + base + ix * scale
instance MemSyn (Imm I AddrSize, Reg R AddrSize, Reg R AddrSize, Size s) where
  mem (i,r1,r2,s) = Mem (Offset i (Just r1) (Just (r2,s)))

-- disp + base + ix * scale
instance MemSyn (Integer, Reg R AddrSize, Reg R AddrSize, Size s) where
  mem (i,r1,r2,s) = mem (Num i :: Imm I AddrSize,r1,r2,s)

-- disp + base + ix * scale
instance MemSyn (String, Reg R AddrSize, Reg R AddrSize, Size s) where
  mem (i,r1,r2,s) = mem (Lab i, r1,r2,s)


