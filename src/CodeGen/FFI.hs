-- | This is our FFI :-)
module CodeGen.FFI where

import CodeGen.Mach
import HAsm

-- Argment generator: given a location, it should produce
-- something that can place the argument at that location.
type ArgGen a = ArgLoc -> a
data ArgLoc   = InReg (Reg R WordSize)
              | OnStack (Arg HAsm.M WordSize)

call_C :: String -> (Integer -> [ArgGen a]) -> ([Instr],[a],[Instr])
call_C fun mk_gens =
  let stack_space = max 0
                   (word_size * (arg_num - fromIntegral (length c_call_regs)))
      gens = mk_gens stack_space
      arg_num = fromIntegral (length gens)
  in ( [ Sub the_size (num stack_space) (Reg reg_stack) ]
     , args 0 c_call_regs gens
     , [ Call (lab fun)
       , Add the_size (num stack_space) (Reg reg_stack)
       ]
     )

  where args off rs (g : gs) = case rs of
          reg : regs -> g (InReg reg) : args off regs gs
          [] -> g (OnStack (arr off reg_stack)) : args (off + word_size) [] gs

        args _ _ []             = []
