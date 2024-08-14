// Derived from src/example-archive/c-testsuite/broken/error-proof/00032.err1.c

int a;
void b() {
  int *c = &a;
  --c;
}
