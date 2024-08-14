
/* CORE FUNCTIONAL STRING DEFINITION */
/*@

datatype strf {
  Strf_E {},
  Strf_NE { u8 head, datatype strf tail }
}

function [rec] (u64) strf_len(strf s) {
  match s {
    Strf_E {} => { 0u64 }
    Strf_NE { head : h , tail : tl } => { 1u64 + strf_len(tl) }
  }
} 

@*/





/* BACKWARDS STRING SEGMENTS FOR ITERATION REASONING */
/*@

datatype str_seg_back {
  StrSegBack_E {},
  StrSegBack_NE { datatype str_seg_back tail, u8 head }
}

function [rec] (bool) contains(str_seg_back s, u8 c) {
  match s {
    StrSegBack_E {} => { false }
    StrSegBack_NE { tail : tl, head : h } => { c == h || contains(tl, c) }
  }
}

function [rec] (datatype strf) seg_strf_concat(datatype str_seg_back front, datatype strf back) {
  match front {
    StrSegBack_E {} => { back }
    StrSegBack_NE { tail : tl, head : h } => { seg_strf_concat(tl, Strf_NE { head : h, tail : back }) }
  }
}

@*/
