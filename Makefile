all:	fstest-driver

fstest-driver:	fstest-driver.o testgen.o

%.o: %.c fstest.h
	$(CC) $< -c -o $@ -std=c99 -Wall -Werror

