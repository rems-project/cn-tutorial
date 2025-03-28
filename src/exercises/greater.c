unsigned int greater (unsigned int p)
/* --BEGIN-- */
/*@ requires p < 10000u32;
    ensures return > p;
@*/
/* --END-- */
{
  return p+42;
}
