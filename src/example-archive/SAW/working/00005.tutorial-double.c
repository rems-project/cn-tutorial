// Tags: simple, bitwise shift, arithmetic
/** Source: SAW Tutorial Examples
 */

/* SAW spec + script

l <- llvm_load_module "double.bc";
double_imp <- llvm_extract l "double_imp";
double_ref <- llvm_extract l "double_ref";
let thm = {{ \x -> double_ref x == double_imp x }};

r <- prove yices thm;
print r;

r <- prove z3 thm;
print r;

let thm_neg = {{ \x -> ~(thm x) }};
write_smtlib2 "double.smt2" thm_neg;

print "Done.";

*/

int double_ref(int x)
  /*@ requires let prod = 2i64 * (i64)x;
               -2147483648i64 <= prod; prod<2147483647i64
      ensures return == (i32) prod  
@*/
{
    return x * 2;
}

int double_imp(int x) 
  /*@ requires let prod = 2i64 * (i64)x;
               0i32 <= x; prod<2147483647i64
      ensures return == (i32) prod
      @*/
{
  return x << 1;
}
