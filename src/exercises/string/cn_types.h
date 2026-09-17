/*
CN string buffer type and predicate.
*/

/*@
// null-terminated strings with (potentially) extra buffer space

datatype String_Buf {
    String_Buf_Nil {
        u64 empty_buf // empty buffer space remaining, including null char
    },
    String_Buf_Cons {
        u8 head, // should not be 0u8
        datatype String_Buf tail
    }
}

// p: pointer to string buffer
// buf_len: length of *entire* buffer, including string
predicate (datatype String_Buf) String_Buf_At(pointer p, u64 buf_len) {
    take h = RW<char>(p);
    take s = String_Buf_Aux(p, buf_len, h);
    assert (buf_len >= 1u64); // there must be space for at least the null char
    return s;
}

// p: pointer to h
// buf_len: length of buffer *including* h
// h: first character of string pointed to by p
predicate (datatype String_Buf) String_Buf_Aux(pointer p, u64 buf_len, u8 h) {
    if (h == 0u8) {
        // everything after h can be write-only
        take rem = each (u64 i; 0u64 < i && i < buf_len) {
            W<char>( array_shift<char>(p, i)) };
        return String_Buf_Nil { empty_buf : buf_len };
    } else {
        take tl_buf = String_Buf_At(array_shift<char>(p, 1u64), buf_len - 1u64);
        return String_Buf_Cons {head : h, tail : tl_buf};
    }
}

@*/
