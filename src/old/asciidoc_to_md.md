# Converting ASCIIDOC to MD

This tutorial was previously written using
[AsciiDoctor](https://asciidoctor.org).  In order to preserve comments, we
manually converted from AsciiDoc to markdown.  The following steps were applied
by hand.

1. Remove `[abstract]\n--`
1. Remove metadata `:...:.*$` lines
1. Convert headers `=` -> `#`
1. Convert links `https://link.me[name]` -> `[name](https://link.me)`
1. Convert inline code `` `+...+` `` -> `` `...` ``
1. Convert code blocks `....` -> `` ``` ``
1. Convert include directives `include_example(path/to/file)`
   ```
   
    ` ` `c title="path/to/file"
    - - 8 < - -
    path/to/file
    - - 8 < - -
    ` ` `

   ```
1. Convert comments `//...` -> `<!-- ... -->`
1. Convert comment blocks
   ```
   ////
   comments...
   ////
   ```
   to
   ```
   <!--
   comments...
   -->
1. Convert images `image::path/to/image[title]` -> `???`
1. Convert enumerated lists `. text` -> `1. text`
1. Convert code blocks
   ```
   [source,c]
   ----
   code
   ----
   ```
1. Convert indented list items
   ```
   * list item with the following indented code W
   +
   [source,c]
   ----
   code
   ----
   ```
