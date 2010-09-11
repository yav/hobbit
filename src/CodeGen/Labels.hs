module CodeGen.Labels where

import Data.List(intersperse)
import CodeGen.Monad(Shape(..))

l_main        = "__main"
l_trace       = "__trace"
l_crash       = "__crash"
l_collector   = "__gc_collector"
l_copy        = "__gc_copy"

l_copy_table  = "__gc_copy_table"
l_scav_table  = "__gc_scav_table"
l_dummy       = "__gc_dummy"
l_scav_globs  = "__gc_scav_glob"

l_scav s      = "__gc_scav_" ++ show (obj_size s) ++ "_"
                             ++ concat (intersperse "_" (map show (obj_ptrs s)))

l_putchar     = "putchar"



