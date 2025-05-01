/*@

datatype String {
    String_Nil {},
    String_Cons { u8 head, datatype String tail}
}

@*/

/*@
// null-terminated strings with (potentially) extra buffer space

datatype String_Buf {
    String_Buf {
        datatype String chars,
        size_t buf_len // full buffer length, including chars
    }
}

predicate (datatype String_Buf) String_Buf_At(pointer p, size_t buf_len) {
    assert (buf_len >= 1u64);
    take h = RW<char>(p);
    take s = String_Aux(p, buf_len, h);
    return String_Buf { chars : s, buf_len : buf_len};
}

// p: pointer to h
// buf_len: length of buffer including h
// h: first character of string starting at p
predicate (datatype String) String_Aux(pointer p, size_t buf_len, u8 h) {
    if (h == 0u8) {
        take rem = each (size_t i; 0u64 < i && i < buf_len - 1u64) {
            W<char>( array_shift<char>(p, i)) };
        return String_Nil {};
    } else {
        take tl_buf = String_Buf_At(array_shift<char>(p, 1u64), buf_len - 1u64);
        return String_Cons {head : h, tail : chars(tl_buf)};
    }
}

@*/
