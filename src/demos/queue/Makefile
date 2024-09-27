.PHONY: clean test cerberus-home

CC?=clang
CN?=cn
CFLAGS?=
DEPS?=
ROOT?=queue

default: exercise

exercise: $(ROOT)_exercise.o
	$(CC) -o $@ $^ $(CFLAGS)

solution: $(ROOT)_solution.o
	$(CC) -o $@ $^ $(CFLAGS)

%.o : %.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

test: $(ROOT)_exercise.c
	# Check for CERBERUS_HOME
	@if [ -z "${CERBERUS_HOME}" ]; \
      then \
        echo "ERROR: Please set CERBERUS_HOME to point to your Cerberus repo."; \
        exit 1; \
      else echo ${CERBERUS_HOME}; \
      fi

	$(CN) instrument $<
	make $(ROOT)_exercise-exec.o cn.o CFLAGS="$(CFLAGS) -I${CERBERUS_HOME}/runtime/libcn/include"
	$(CC) -o $@ $(ROOT)_exercise-exec.o cn.o $(CFLAGS)

verify:
	$(CN) verify $(ROOT)_exercise.c

clean:
	rm -f exercise solution cn.c cn.h stdlib.h *-exec.c *.o
