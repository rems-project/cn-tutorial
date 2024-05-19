// Currently unprovable: do-while not supported 

int
main()
/*@ ensures return == 0i32; @*/
{
  int c;
  c = 0;
  do
    ;
  while (0);
  return c;
}
