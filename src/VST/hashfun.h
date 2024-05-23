// hashfun.h
#include "strfun.h"

/*@
function [rec] (u32) hashf_aux(u32 h, strf s) {
    match s {
        Strf_E {} => { h }
        Strf_NE { head : c, tail : cs } => {
            if ((u32) c >= 128u32) {
                hashf_aux (h * 65599u32 + (u32) c, cs)
            } else {
                hashf_aux (h * 65599u32 + 1u32 - (u32) c, cs)
            }
        }
    }
}

function (u32) hashf (strf s) {
    hashf_aux(0u32, s)
}

function (u64) N () {
    109u64
}
  
datatype cellf {
    Cellf_E {},
    Cellf_NE {strf key, u32 count, cellf next}
}

datatype hashtablef {
    Hashtablef_E {},
    Hashtablef_NE {datatype cellf head, datatype hashtablef tail}
}

function [rec] (datatype hashtablef) repeat_empty_cellf (u64 n) {
    if (n <= 0u64) {
        Hashtablef_E {}
    }
    else {
        Hashtablef_NE {head : Cellf_E {}, tail : repeat_empty_cellf (n - 1u64) }
    }
}

function (datatype hashtablef) empty_tablef () {
    repeat_empty_cellf(N())
}

function [rec] (u32) list_getf (strf s, datatype cellf b) {
    match b {
        Cellf_E {} => { 0u32 }
        Cellf_NE { key : k, count : c, next : n} => {
            if (k == s) {
                c
            }
            else {
                list_getf(s, n)
            }
        }
    }
}

function [rec] (datatype cellf) list_incrf (strf s, datatype cellf b) {
    match b {
        Cellf_E {} => { Cellf_NE { key : s , count : 1u32, next : Cellf_E {} } }
        Cellf_NE { key : k, count : c, next : n } => {
            if (k == s) {
                Cellf_NE { key : k , count : c + 1u32, next : n }
            }
            else {
                Cellf_NE {  key : k , count : c , next : list_incrf(s, n) }
            }
        }
    }
}

function [rec] (u32) num_bucketsf (datatype hashtablef contents) {
    match contents {
        Hashtablef_E {} => { 0u32 }
        Hashtablef_NE { head : h, tail : t } => {
            1u32 + num_bucketsf (t)
        }
    }
}

function [rec] (datatype cellf) get_bucketf (u32 n, datatype hashtablef contents) {
    match contents {
        Hashtablef_E {} => { Cellf_E {} }
        Hashtablef_NE { head : h, tail : t } => {
            if (n == 0u32) {
                h
            }
            else {
                get_bucketf(n - 1u32, t)
            }
        }
    }
}

function [rec] (datatype hashtablef) update_bucketf (u32 n, datatype hashtablef contents, datatype cellf b) {
    match contents {
        Hashtablef_E {} => { Hashtablef_E {} }
        Hashtablef_NE { head : h, tail : t } => {
            if (n == 0u32) {
                Hashtablef_NE { head : b , tail : t }
            }
            else {
                Hashtablef_NE { head : h, tail : update_bucketf(n - 1u32, t, b) }
            }
        }
    }
}

function [rec] (u32) modulo_u32f (u32 n, u32 m) {
    if (n < m) {
        n
    }
    else {
        modulo_u32f (n - m, m)
    }
}

function (u32) hashtablef_get (strf s, datatype hashtablef contents) {
    list_getf(s, get_bucketf(modulo_u32f(hashf(s), num_bucketsf(contents)), contents))
}

function (datatype hashtablef) hashtablef_incr (strf s, datatype hashtablef contents) {
    let h = hashf(s);
    let al = get_bucketf(modulo_u32f(h, num_bucketsf(contents)), contents);
    update_bucketf(modulo_u32f(h, num_bucketsf(contents)), contents, list_incrf(s, al))
}

@*/
