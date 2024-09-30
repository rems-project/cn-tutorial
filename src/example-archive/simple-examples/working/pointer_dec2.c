// Derived from src/example-archive/c-testsuite/broken/error-proof/00032.err1.c

int a[2];
void b() {
  int *c = &a[1];
  --c;
}
