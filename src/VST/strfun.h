/*@
datatype strf {
  Strf_E {},
  Strf_NE {u8 head, datatype strf tail}
}

function [rec] (u64) strf_len (strf s) {
  match s {
    Strf_E {} => { 0u64 }
    Strf_NE { head : h , tail : t } => { 1u64 + strf_len(t) }
  }
} 

function [rec] (u8) strf_get(strf s, u64 i) {
  match s {
    Strf_E {} => { 0u8 }
    Strf_NE { head : h , tail : t } => { 
      if (i == 0u64) {
        h
      }
      else {
        strf_get(t, i - 1u64)
      }
     }
  }
}

@*/
