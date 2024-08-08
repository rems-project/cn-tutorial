// Example of negating a long integer literal. Broken as of 2024-7-4. 
// See: https://github.com/rems-project/cerberus/issues/257

// Type error: 
void long_type_err_1() { 
  -1l; 
  return; 
}