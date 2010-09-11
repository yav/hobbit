OBJS	= common.o asm.o 

rts_common.a: ${OBJS}
	ar -rc -o rts_common.a ${OBJS}

common.o: config.h rts.h common.c
	gcc -c common.c

asm.o: config.h asm.S
	gcc -c asm.S

clean:
	-rm ${OBJS}

veryclean: clean
	-rm rts_common.a
	
