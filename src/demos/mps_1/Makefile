.PHONY: clean test

CC=clang
DEPS=mps_1.h
ROOT=mps_1
CN_TEST=~/sandboxes/cerberus/tests/cn-runtime/cn-runtime-single-file.sh

default: exercise

exercise: $(ROOT)_exercise.o
	$(CC) -o $@ $^ $(CFLAGS)

solution: $(ROOT)_solution.o
	$(CC) -o $@ $^ $(CFLAGS)

%.o : %.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

test:
	$(CN_TEST) mps_1_exercise.c || true

clean:
	rm -f exercise solution *.o
