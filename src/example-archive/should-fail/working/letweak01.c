
int
f (int x) {
  x = (x = 1);

  return x + 2;
}

int main(void) {
  f(406);
}