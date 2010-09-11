rts.ps: rts.dvi
	dvips rts

rts.dvi: rts.tex
	latex rts

clean:
	-rm *.log *.aux

veryclean: clean
	-rm rts.dvi rts.ps
	
