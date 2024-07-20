/** Get the first element of a zeroed, nonempty array */
int head(int *arr, unsigned long len)
/*@
requires
    take arr_in = each(u64 i; i < len) {
        Owned(array_shift<int>(arr, i))
    };
    each(u64 i; i < len) {
        arr_in[i] == 0i32
    };
    len > 0u64;

ensures
    take arr_out = each(u64 i; i < len) {
        Owned(array_shift<int>(arr, i))
    };
    each(u64 i; i < len) {
        arr_out[i] == 0i32
    };
    return == 0i32;
@*/
{
    unsigned long idx = 0;
    
    // First, we apply `extract` to direct CN to the relevant element of the
    // iterated resource `arr_in`, which it needs in order to verify the
    // following read:
    /*@ extract Owned<int>, idx; @*/

    int hd = arr[idx];

    // Now, we need to demonstrate that `hd` is zero in order to return it and
    // satisfy the third `ensures` clause. To do so, we should think of our
    // second `requires` clause as introducing a quantified constraint, which is
    // approximately `forall i. len > i ==> arr_in[i] == 0` (`==>` being logical
    // implication). In order to leverage this constraint, we need to
    // instantiate `i` with our choice of index `idx`:
    /*@ instantiate idx; @*/

    // Now, our constraint has evolved into `len > 0 ==> arr_in[0] == 0`. From
    // here, verification of this constraint can proceed automatically. (Recall
    // that we already required that `len > 0u64`.)
    return hd;
}
