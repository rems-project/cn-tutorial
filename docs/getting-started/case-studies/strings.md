# Null-terminated strings

A null-terminated string is an array of characters where the 0 character,
`'\0'`, signals the end of the string. (Note that there is no "null" in the
usual pointer sense, just the byte consisting of all zeros. Note also that this
is distinct from `'0'`.)

To ensure safety for operations like in-place concatenation, we need to keep
track of not just the string up to `'\0'`, but the entire buffer allocated for
the string. This means our logical representation of strings looks like this:

```c title="exercises/string/cn_types.h"
--8<--
exercises/string/cn_types.h
--8<--
```

In order to facilitate proofs, we define logical string buffers inductively. A
string buffer represents either the empty string, in which case we have a
64-bit integer indicating how many unused bytes the buffer has (counting the
null byte as unused), or a nonempty string, in which case we have a (non-null)
character followed by another string buffer.

Due to CN restrictions on top-level `if`, we have two mutually-recursive
predicates. `String_Buf_At(p, buf_len)` asserts that at the input pointer `p`,
there is a buffer of total size `buf_len` (including the string, the `'\0'`
terminator, and any extra empty bytes), represented by the logical string that
`String_Buf_At` returns. (Note that `buf_len` must be at least 1, to have space
for at least `'\0'`.) `String_Buf_At` reads the first character and, via
`String_Buf_Aux`, checks if it is `'\0'`. If so, it blocks the rest of the
bytes, using `W` instead of `RW` because these bytes have no meaningful data
for us to read yet. If the first byte is not `'\0'`, we recursively call
`String_Buf_At` on the rest of the buffer.

`spec_funs.h` contains CN functions on the logical representation of string
buffers. Specifically:
* `buf_len` gets the length of the entire allocated buffer for the string
* `string_length` gets the length of the conceptual string, i.e., all the
characters before `'\0'`
* `empty_buf_len` gets the number of bytes after the conceptual string, i.e.,
the number of bytes in the buffer starting with the first `'\0'`
* `string_buf_concat` performs in-place concatenation of two strings. It
assumes the destination string has sufficient space
* `string_buf_nth` returns the (0-indexed) nth character of a string,
defaulting to `'\0'` if n is greater than or equal to the length of the
conceptual string
* `is_nil_string_buf` checks if a string buffer represents the empty string
* `string_equal` checks if two string buffers contain equal conceptual strings,
i.e., the buffers may have different total size, but they should contain the
same characters up to and including the first `'\0'`

`string_buf.c` contains specifications for string functions in the C standard
library. The functions we would like to have available are `malloc`, `free`,
`strlen`, `strcpy`, `strcmp`, and `strcat`. However, to work with our
`String_Buf` type and ensure memory safety, we add additional arguments to
keep track of the lengths of all of the strings' buffers.

`trusted.h` and `lemmas.c` both contain lemmas about the functions in
`spec_funs.h` and `string_buf.c`. The lemmas in `trusted.h` are trusted,
i.e., not proven in CN, while the ones in `lemmas.c` are proven in CN.
These will be useful for the example function in `example.c`.

`example.c` contains a toy function designed to use every function in
`string_buf.c` together. It takes a pointer to an input string, the length of
the buffer containing that string, the number of bytes we will allocate for
a second string, and two characters. To make the later copies and comparisons
interesting, we require the input string to be nonempty and the characters
distinct and non-null. We will also later concatenate the strings, so we want
enough space in the buffer we will allocate to fit the input string twice (with
room for a terminating `'\0'` also). We specify this with the constraint
`string_len(sIn) + string_len(sIn) < n2`, and we require the input string to be
sufficiently small that this statement is meaningful, i.e., the `+` is not
wrapping around.

In the body of our function, we first allocate the second string using
`malloc_str`. Like `malloc`, this does not initialize the bytes in the string to
any specific value.

Next, we copy the input string into the second string's buffer. Thanks to our
preconditions, we know we have enough space for this.

After that, we compare the two strings. Because we just copied the first into
the second, the result should be 0; we confirm with `assert` that it is.

We would now like to edit the first character of each string. We have a safe
wrapper for array edits, `edit_array_at`. This ensures not only that we do
not write beyond the bounds of our array, but also that our edit is meaningful:
we must edit a character within the current defined string, not the empty
buffer space. (If we wanted to extend the string, we would use
`string_buf_cat`.) However, in order to do this, we need to switch from our
`String_Buf` representation of strings to an array representation of strings.

Luckily, we have a lemma for this, `string_buf_to_array`. When we go to edit
the first array, however, we will need to know that the index at which we are
writing is less than the string length. We are writing at index `0`, so the
lemma that tells us this is `nonempty_string_len`, which asserts that nonempty
strings have positive length. This lemma is stated in terms of our
`String_Buf_At` predicate, so we need to apply it before applying
`string_buf_to_array`.

This allows us to edit the array, but when we go to convert it back to a
`String_Buf`, we will need additional information. In order for an array to
be a valid string buffer, it must start with some number (potentially 0) of
non-null characters, in this case `s1Len - 1` of them, followed by the null
character, followed by 0 or more write-only bytes. We have a lemma stating
that the first `s1Len - 1` characters of the array are non-null,
`nonzero_up_to_len`, but again, it is stated in terms of `String_Buf` and
`String_Buf_At`, so we must apply it before `string_buf_to_array`.

We now wish to edit the first character of the second string. Again, we will
need `nonzero_up_to_len` for the conversion back to a `String_Buf`. Before
that, though, how do we know that the length of this second string is positive?
We previously compared it to the first string and got `0`, so we know the two
strings were equal at that point, and we showed that the first string has
nonzero length. That means we can apply `string_equal_impl_equal_len` before
editing the first string to assert that the second string has nonzero length
as well.

Next, we concatenate the two strings. We know from the lemmas we just applied
and the precondition that the sum of the two strings' lengths is less than
the number of bytes in the second string's buffer, so the in-place
concatenation will not write beyond the end of the buffer.

Finally, we free the two strings. The only precondition for this is ownership,
so there is nothing to prove.