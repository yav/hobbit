OBJS	= gc.o asm.o main.o
CC	= gcc -Wall -g

rts.a: $(OBJS)
	ar -rc -o rts.a $(OBJS)

main.o: config.h rts.h main.c
	$(CC) -c main.c

gc.o: config.h rts.h gc.c
	$(CC) -c gc.c

asm.o: config.h asm.S
	$(CC) -c asm.S

clean:
	-rm $(OBJS)

veryclean: clean
	-rm rts.a
