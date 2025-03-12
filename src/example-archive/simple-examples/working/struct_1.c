// Assign 0 to a struct field. The proof shows the other field is unchanged.

struct s
{
  int x;
  int y;
};

void struct_1(struct s *p)
/*@ requires take StructPre  = RW<struct s>(p); @*/
/*@ ensures  
      take StructPost = RW<struct s>(p);
      StructPre.x == StructPost.x;
      StructPost.y == 0i32; @*/
{
  p->y = 0;
  // p->x = 7;  // <-- This would fail
}
