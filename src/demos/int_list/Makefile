.PHONY: clean test

CC=clang
DEPS=int_list.h
ROOT=int_list
CN_TEST=~/sandboxes/cerberus/tests/cn-runtime/cn-runtime-single-file.sh

default: exercise

exercise: $(ROOT)_exercise.o
	$(CC) -o $@ $^ $(CFLAGS)

solution: $(ROOT)_solution.o
	$(CC) -o $@ $^ $(CFLAGS)

%.o : %.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

test:
	$(CN_TEST) $(ROOT)_exercise.c || true

verify:
	cn verify $(ROOT)_exercise.c

clean:
	rm -f exercise solution *.o
