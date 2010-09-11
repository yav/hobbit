include Makefile.local

GHC_FILES	= GHC_files
GHC_FILES_PROF	= GHC_files_prof

COMMON_OPTS 	= -W -fglasgow-exts -fallow-undecidable-instances -ihasm -iUtils
OPTS		= $(COMMON_OPTS) -hidir $(GHC_FILES) -odir $(GHC_FILES) 
POPTS		= $(COMMON_OPTS) +RTS -K10M -RTS \
		-hidir $(GHC_FILES_PROF) \
		-odir $(GHC_FILES_PROF) \
		-prof -auto-all

FILES	= Parsing/Lexer.hs Parsing/Parser.hs \
	*.hs *.lhs \
	Parsing/*.hs \
	AST/*.hs \
	ModSys/*.lhs ModSys/*.hs \
	Type/*.hs Type/*.lhs \
	Depend/*.hs \
	CodeGen/*.hs \
        hasm/*.hs \
	UI/*.hs 
	

hc: $(GHC_FILES) $(FILES)
	$(GHC) --make $(OPTS) -o hc Interact.hs

hc_prof: $(GHC_FILES_PROF) $(FILES)
	$(GHC) --make $(POPTS) -o hc_prof Interact.hs

ccTest: GHC_files Parsing/SIL.hs $(FILES)
	$(GHC) --make $(OPTS) -o ccTest CC/Test.hs

Parsing/Lexer.hs : Parsing/Lexer.x
	$(ALEX) Parsing/Lexer.x -o Parsing/Lexer.hs

Parsing/Parser.hs : Parsing/Parser.y
	$(HAPPY) Parsing/Parser.y

$(GHC_FILES):
	mkdir $(GHC_FILES)

$(GHC_FILES_PROF):
	mkdir $(GHC_FILES_PROF)

clean:
	-rm -rf $(GHC_FILES) $(GHC_FILES_PROF)

veryclean: clean
	-rm Parsing/Parser.hs Parsing/Lexer.hs Parsing/SIL.hs
	


