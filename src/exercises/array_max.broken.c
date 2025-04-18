unsigned int array_max (unsigned int *p, unsigned int n)
{
  int max = 0;

  int i;
  for (i = 1; i <= n; i++) {
    if (p[i] > max) {
      max = p[i];
    }
  }

  return max;
}