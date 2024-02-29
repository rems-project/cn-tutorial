changequote(`{{',`}}')

define({{prefix_filename}},// {{$1}}
{{$2}})

define({{include_example}},```c
{{prefix_filename($1,builtin(include,$1))}}
```)
