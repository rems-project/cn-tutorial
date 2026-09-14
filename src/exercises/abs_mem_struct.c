int abs_mem (int *p)
/* --BEGIN-- */
/*@ requires take x = RW<int>(p);
             MINi32() < x;
    ensures take x2 = RW<int>(p);
            x == x2;
            return == ((x >= 0) ? x : (0-x));
@*/
/* --END-- */
{
  int x = *p;
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}



struct tuple {
  int x;
  int y;
};


int abs_y (struct tuple *p)
/*@ requires take s = RW(p);
             MINi32() < s.y;
    ensures  take s2 = RW(p);
             s == s2;
             return == ((s.y >= 0) ? s.y : (0-s.y));
@*/
{
  return abs_mem(&p->y);
}

void* cn_malloc(unsigned long size);

int main(void) {
  int x = 5;
  int abs_x = abs_mem(&x);

  struct tuple *t = cn_malloc(sizeof(struct tuple));
  t->x = 4;
  t->y = 3;
  int abs_t = abs_y(t);
}
