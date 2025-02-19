return code: 1
./src/example-archive/dafny-tutorial/broken/error-proof/fib.c:21:19: error: Type error
/*@ requires 0 <= n; @*/
                  ^
Expression 'n' has type 'i32'.
I expected it to have type 'integer' because of ./src/example-archive/dafny-tutorial/broken/error-proof/fib.c:21:14:
/*@ requires 0 <= n; @*/
             ^
