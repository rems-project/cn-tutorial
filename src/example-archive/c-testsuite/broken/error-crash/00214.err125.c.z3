return code: 125
unsupported: ./src/example-archive/c-testsuite/broken/error-crash/00214.err125.c:42:4:: GCC statements as expressions not yet supported
internal error: ./src/example-archive/c-testsuite/broken/error-crash/00214.err125.c:42:4:: GCC statements as expressions not yet supported
cn: internal error, uncaught exception:
    Failure("internal error: ./src/example-archive/c-testsuite/broken/error-crash/00214.err125.c:42:4:: GCC statements as expressions not yet supported")
    Raised at Stdlib.failwith in file "stdlib.ml", line 29, characters 17-33
    Called from Cerb_frontend__Translation.translate in file "ocaml_frontend/generated/translation.ml", line 4452, characters 4-92
    Called from Cerb_backend__Pipeline.c_frontend_and_elaboration.(fun) in file "backend/common/pipeline.ml", line 245, characters 18-92
    Called from Dune__exe__Main.frontend in file "backend/cn/bin/main.ml", line 77, characters 4-81
    Called from Dune__exe__Main.with_well_formedness_check in file "backend/cn/bin/main.ml", lines 144-150, characters 6-36
    Called from Cmdliner_term.app.(fun) in file "cmdliner_term.ml", line 24, characters 19-24
    Called from Cmdliner_eval.run_parser in file "cmdliner_eval.ml", line 35, characters 37-44
