return code: 1
[1/5]: ffs_ref -- fail
[2/5]: ffs_imp -- pass
[3/5]: ffs_imp_nobranch -- pass
[4/5]: ffs_bug -- pass
[5/5]: ffs_musl -- fail
./src/example-archive/SAW/broken/error-proof/00006.tutorial-ffs.c:42:19: error: Undefined behaviour
        if(((1 << i++) & word) != 0)
                  ~^~ 
an exceptional condition occurs during the evaluation of an expression (§6.5#5)
State file: file:///tmp/state__00006.tutorial-ffs.c__ffs_ref.html
./src/example-archive/SAW/broken/error-proof/00006.tutorial-ffs.c:103:14: error: Missing resource for reading
  return x ? debruijn32[(x&-x)*0x076be629 >> 27]+1 : 0;
             ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
Resource needed: Owned<char>(&(&&debruijn32[(u64)0'i32])[(u64)(
                                                           !(
                                                             0'i32
                                                             <= 27'i32 /* 0x1b */
                                                             && true
                                                           ) ? 0'u32 :
                                                           (
                                                             (x & 0'u32 - x)
                                                             * (u32)124511785'i32 /* 0x76be629 */
                                                             >> (u32)27'i32 /* 0x1b */
                                                           )
                                                         )])
State file: file:///tmp/state__00006.tutorial-ffs.c__ffs_musl.html
