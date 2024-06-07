#include <stddef.h>
#include "hashtable.c"
#include "util.c"

// extern unsigned int hash (char *s);
// /*@
// spec hash (pointer s);
// requires
//   take sIn = Stringa(s);
// ensures
//   take sOut = Stringa(s);
//   sIn == sOut;
//   return == hashf(sIn);
// @*/

unsigned int hash (char *s)
/*@
requires
  take sIn = Stringa(s);
ensures
  take sOut = Stringa(s);
  sIn == sOut;
  return == hashf(sIn);
@*/
{
  unsigned int n=0;
  size_t i=0;
  /*@ apply elems_owned(s); @*/
  char c = s[i];
  while (c)      
  /*@ 
    inv 
      //take sInv = Stringa(s);
      //sInv == sIn;
      i <= strf_len(sIn);
      take sInv = each(u64 j; j <= strf_len(sIn)) { Owned<char>(array_shift<char>(s, j)) };
      each (u64 j; j < strf_len(sIn)) { sInv[j] != 0u8 };
      sInv[strf_len(sIn)] == 0u8;
      c == sInv[i];
      c == 0u8 || i < strf_len(sIn);
  @*/
  {
    /*@ assert (c != 0u8); @*/
    /*@ assert (i < strf_len(sIn)); @*/
    n = n*65599u+(unsigned)c;
    i++;
    /*@ assert (i <= strf_len(sIn)); @*/
    /*@ extract Owned<char>, i; @*/
    c=s[i];
  }
  return n;
}

char *copy_string (char *s) 
/*@
requires
  take sIn = Stringa(s);
  strf_len(sIn) + 1u64 != 0u64;
ensures
  take sOut = Stringa(s);
  take dOut = Stringa(return);
  sIn == sOut;
  dOut == sOut;
@*/
{
  char *p = malloc_str(strlen(s) + (unsigned int) 1);
  if (!p) exit(1);
  strcpy(p,s);
  return p;
}

// struct hashtable *new_table (void)
// /*@
// requires
//   true;
// ensures
//   take h = Hashtable(return);
//   h == empty_tablef();
// @*/
// {
//   int i;
//   struct hashtable *p = malloc_hashtable();
//   if (!p) exit(1);
//   for (i=0; i<N; i++) 
//   /*@
//     inv
//       take hInv = Hashtable(p);
//   @*/
//   {
//     p->buckets[i]=NULL;
//   }
//   return p;
// }  

struct cell *new_cell (char *key, unsigned int count, struct cell *next)
/*@
requires
  take keyIn = Stringa(key);
  take nextIn = Cells(next);
ensures
  take cellsOut = Cells(return);
  cellsOut == Cellf_NE { key : keyIn, count : count, next : nextIn };
@*/
{
  struct cell *p = malloc_cell();
  if (!p) exit(1);
  p->key = copy_string(key);
  p->count = count;
  p->next = next;
  return p;
}

// unsigned int get (struct hashtable *table, char *s) 
// /*@
// requires
//   take tableIn = Hashtable(table);
//   take sIn = Stringa(s);
// ensures
//   take tableOut = Hashtable(table);
//   take sOut = Stringa(s);
//   //tableIn == tableOut;
//   sIn == sOut;
//   return == hashtablef_get(sOut, tableOut);
//   @*/
// {
//   unsigned int h = hash(s);
//   unsigned int b = 0; //modu32(h, N);
//   struct cell** bs = table->buckets;
//   /* extract Owned<struct cell *>, b; */
//   struct cell *p = bs[b];
//   while (p) {
//     if (strcmp(p->key, s)==0)
//       return p->count;
//     p=p->next;
//   }
//   return 0;
// }

extern void incr_list (struct cell *r0, char *s); 
/*@
spec incr_list (pointer r0, pointer s);
requires
  take cellIn = Cells(r0);
  take sIn = Stringa(s);
  (u64) list_getf(sIn, cellIn) < u32max();
ensures
  take cellOut = Cells(r0);
  take sOut = Stringa(s);
  sIn == sOut;
  cellOut == list_incrf(sIn, cellIn);
@*/
// {
//   struct cell *p, **r;
//   for(r=r0; ; r=&p->next) {
//     p = *r;
//     if (!p) {
//       *r = new_cell(s, 1, NULL);
//       return;
//     }
//     if (strcmp(p->key, s)==0) {
//       p->count++;
//       return;
//     }
//   }
// }  

// void incr (struct hashtable *table, char *s)
// /*@
// requires
//   take tableIn = Hashtable(table);
//   take sIn = Stringa(s);
//   //(u64) hashtablef_get(sIn, tableIn) < u32max();
// ensures
//   take tableOut = Hashtable(table);
//   take sOut = Stringa(s);
//   sIn == sOut;
//   //tableOut == hashtablef_incr(sIn, tableIn);
// @*/
// {
//   unsigned int h = hash(s);
//   unsigned int b = 0; // modu32(h, N);
//   struct cell ** bs = table->buckets;
//   /*@ extract Owned<struct cell *>, b; @*/
//   struct cell * clist = table->buckets[b];
//   incr_list (clist, s);
// }

// void incrx (struct hashtable *table, char *s)
// /*@
// requires
//   take tableIn = Hashtable(table);
//   take sIn = Stringa(s);
//   (u64) hashtablef_get(sIn, tableIn) < u32max();
// ensures
//   take tableOut = Hashtable(table);
//   take sOut = Stringa(s);
//   sIn == sOut;
//   tableOut == hashtablef_incr(sIn, tableIn);
// @*/
// {
//   unsigned int h = hash(s);
//   unsigned int b = modu32(h, N);
//   struct cell ** bs = table->buckets;
//   /*@ assert (b < (u32) N); @*/
//   /*@ extract Owned<struct cell *>, b; @*/
//   struct cell *p = bs[b];
//   while (p) {
//     if (strcmp(p->key, s)==0) {
//       p->count++;
//       return;
//     }
//     p=p->next;
//   }
//   bs[b]=new_cell(s, 1, bs[b]);
// }
