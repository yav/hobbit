OBJS = ../asm.o ../common.o rts.o linux_asm.o


rts.a: ${OBJS}
	ar -rc rts.a ${OBJS}

rts.o: ../rts.h ../config.h rts.c
	gcc -v -o rts.o -c rts.c

linux_asm.o: linux_asm.s
	as linux_asm.s -o linux_asm.o

../asm.o ../common.o ::
	make -C ..

clean:
	-rm rts.a ${OBJS}


