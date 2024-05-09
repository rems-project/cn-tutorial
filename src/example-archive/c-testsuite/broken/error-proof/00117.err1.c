/*
error: TODO: WellTyped infer_pexpr

PEctor <other location (Cabs_to_ail.constructValue)>
|-Array
|-Pexpr(TODO) <other location (Cabs_to_ail.constructValue)>
| `-Array(conv_loaded_int(''signed int'', a_475),
conv_loaded_int(''signed int'', a_476))
`-Pexpr(TODO) <other location (Cabs_to_ail.constructValue)>
  `-Array(conv_loaded_int(''signed int'', a_475),
conv_loaded_int(''signed int'', a_476))

cn: internal error, uncaught exception:
    Failure("TODO: WellTyped infer_pexpr")
*/
// Cause: unknown 

int main()
{
	int x[] = { 1, 0 };
	return x[1];
}
