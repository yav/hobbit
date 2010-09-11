module Type.Instances(parseRuleEnv) where

import AST
import Pass
import Parser (parse,aRule)
import Parsing.Fixity
import Opts
import Utils


rule txt f          = do p <- parse aRule txt
                         return (Rule f p)

rule0 x f           = rule x (\[] -> f)
rule1 x f           = rule x (\[x] -> f x)
rule2 x f           = rule x (\[x,y] -> f x y)


parseRuleEnv       :: Pass RuleEnv
parseRuleEnv        = RuleEnv # parseSupers <# parseInsts


-- XXX: At the moment I have manullay computed the multiple rules and closures.
-- This should be autoamted at some point.
parseSupers :: Pass [Rule]
parseSupers = mapM rewrite =<< sequence
  [ rule1 "Ord a => Eq a" (simpEv . ordToEqEv)

  , rule1 "(a # b = c) => Width a" (simpEv . projEv 0)
  , rule1 "(a # b = c) => DNat a" (simpEv . projEv 0)
  , rule1 "(a # b = c) => Width b" (simpEv . projEv 1)
  , rule1 "(a # b = c) => DNat b" (simpEv . projEv 1)
  , rule1 "(a # b = c) => Width c" 
                            (\e -> simpEv (plusEv (projEv 0 e) (projEv 1 e)))
  , rule1 "(a # b = c) => DNat c" 
                            (\e -> simpEv (plusEv (projEv 0 e) (projEv 1 e)))
  , rule1 "(a # b = c) => (a + b = c)" (\_ -> dummyEv)

  , rule1 "BitRep t n => Width n" id
  , rule1 "BitRep t n => DNat n" id
  , rule1 "BitData t n => BitRep t n" id
  , rule1 "BitData t n => Width n" id
  , rule1 "BitData t n => DNat n" id

  , rule1 "Align n => DNat n" id
  , rule1 "Index n => DNat n" id
  , rule1 "Width n => DNat n" id

  , rule1 "SizeOf t n => DNat n" id

  , rule1 "UpdField l r t => Field l r t" id
  ] 



parseInsts :: Pass [Rule]
parseInsts = mapM rewrite =<< sequence
  [ rule1 "Width n => Literal (Bit n)" litBitEv     
  , rule1 "Index n => Literal (Ix n)"  litIxEv        

  , rule1 "Width n => Eq (Bit n)"       eqBitEv            
  , rule0 "Eq (Ix n)"                   eqIxEv              
  , rule0 "Eq (ARef n a)"               eqPtrEv           
  , rule0 "Eq (APtr n a)"               eqPtrEv           

  , rule1 "Width n => Ord (Bit n)"      ordBitEv          
  , rule1 "Index n => Ord (Ix n)"       (\_ -> ordIxEv)

  , rule1 "Width n => Num (Bit n)"      numBitEv          
 
  , rule1 "Width n => BitOps (Bit n)"   bitOpsBitEv    

  , rule1 "Width n => Bounded (Bit n)"  boundedBitEv  
  , rule1 "Index n => Bounded (Ix n)"   boundedIxEv    

  , rule1 "Width n => BitRep (Bit n)    n"          id                 
  , rule0            "BitRep (Ix n)     MaxWidth"   (IntEv maxWidth)    
  , rule0            "BitRep (ARef n a) MaxWidth"   (IntEv maxWidth)  
  , rule0            "BitRep (APtr n a) MaxWidth"   (IntEv maxWidth)  

  , rule1 "Width n => BitData (Bit n)   n"          id

  , rule0            "ValIn (LE (Bit 0))  (Bit 0)"  (leEv (IntEv 0))
  , rule0            "ValIn (LE (Bit 8))  (Bit 8)"  (leEv (IntEv 1))
  , rule0            "ValIn (LE (Bit 16)) (Bit 16)" (leEv (IntEv 2))
  , rule0            "ValIn (LE (Bit 24)) (Bit 24)" (leEv (IntEv 3))
  , rule0            "ValIn (LE (Bit 32)) (Bit 32)" (leEv (IntEv 4))
  , rule1 "Index n => ValIn (LE (Ix n)) (Ix n)"     (\_ -> leEv (IntEv 4))
  , rule0            "ValIn (LE (APtr a r)) (APtr a r)" (leEv (IntEv 4))

  , rule0            "ValIn (BE (Bit 0))  (Bit 0)"  (beEv (IntEv 0))
  , rule0            "ValIn (BE (Bit 8))  (Bit 8)"  (beEv (IntEv 1))
  , rule0            "ValIn (BE (Bit 16)) (Bit 16)" (beEv (IntEv 2))
  , rule0            "ValIn (BE (Bit 24)) (Bit 24)" (beEv (IntEv 3))
  , rule0            "ValIn (BE (Bit 32)) (Bit 32)" (beEv (IntEv 4))
  , rule1 "Index n => ValIn (BE (Ix n)) (Ix n)"     (\_ -> beEv (IntEv 4))
  , rule0            "ValIn (BE (APtr a r)) (APtr a r)" (beEv (IntEv 4))

  , rule0            "SizeOf (LE (Bit  0)) 0" (IntEv 0)
  , rule0            "SizeOf (LE (Bit  8)) 1" (IntEv 1)
  , rule0            "SizeOf (LE (Bit 16)) 2" (IntEv 2)
  , rule0            "SizeOf (LE (Bit 24)) 3" (IntEv 3)
  , rule0            "SizeOf (LE (Bit 32)) 4" (IntEv 4)
  , rule1 "Index n => SizeOf (LE (Ix n)) 4"   (\_ -> IntEv 4)
  , rule0            "SizeOf (LE (APtr a r)) 4" (IntEv 4)

  , rule0            "SizeOf (BE (Bit  0)) 0" (IntEv 0)
  , rule0            "SizeOf (BE (Bit  8)) 1" (IntEv 1)
  , rule0            "SizeOf (BE (Bit 16)) 2" (IntEv 2)
  , rule0            "SizeOf (BE (Bit 24)) 3" (IntEv 3)
  , rule0            "SizeOf (BE (Bit 32)) 4" (IntEv 4)
  , rule1 "Index n => SizeOf (BE (Ix n)) 4"   (\_ -> IntEv 4)
  , rule0            "SizeOf (BE (APtr a r)) 4" (IntEv 4)


  , rule "(SizeOf a x, DNat i, x * i = n) => SizeOf (Array i a) n"
                                          (\[x,y,_] -> simpEv (mulEv x y)) 
                    
  , rule "(Width t1, Width t2, Width t3, t1 + t2 = t3) => t1 # t2 = t3"
                                          (\[x,y,_,_] -> joinEv x y) 

  , rule1 "BitData t n => Bytes (LE t)"       (\_ -> dummyEv)
  , rule1 "BitData t n => Bytes (BE t)"       (\_ -> dummyEv)
  , rule1 "Bytes a     => Bytes (Array n a)"  (\_ -> dummyEv)

  , rule2 "(SizeOf a m, Align n) => AreaDecl (ARef n a)" areaEv
  ]

                        
