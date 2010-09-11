module CodeGen.Mach where

import HAsm

reg_A :: Reg R WordSize
reg_A     = RAX

reg_C :: Reg R WordSize
reg_C     = RCX

reg_D :: Reg R WordSize
reg_D     = RDX

reg_stack :: Reg R WordSize
reg_stack = RSP

reg_src :: Reg R WordSize
reg_src   = RSI

reg_dst :: Reg R WordSize
reg_dst   = RDI

reg_base :: Reg R WordSize
reg_base  = RBP

is_reg_stack :: Reg R AddrSize -> Bool
is_reg_stack RSP = True
is_reg_stack _ = False

is_reg_C :: Reg R WordSize -> Bool
is_reg_C RCX = True
is_reg_C _   = False

c_call_regs = [ RDI, RSI, RDX, RCX, R8, R9 ]


--------------------------------------------------------------------------------
type WordSize = AddrSize

word :: Size WordSize
word = addr

word_size :: Integer
word_size = bytes word

arr :: Integer -> Reg R WordSize -> Arg M WordSize
arr n r = mem (word_size * n, r)

word_size_bits = 8 * word_size
lower_half_mask = 2^(word_size_bits `div` 2) - 1

class IsSize s where
  the_size :: Size s


instance IsSize B1 where the_size = B1
instance IsSize B2 where the_size = B2
instance IsSize B4 where the_size = B4
instance IsSize B8 where the_size = B8

