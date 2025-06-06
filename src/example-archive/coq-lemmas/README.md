# Coq Examples

CN examples using lemmas that can be extracted to Coq. The examples
are split into:

- Trivial - named `trivial-*.c`
- Recursive - named `recursive-*.c` _(export for these examples is not supported by CN yet)_

Some examples are accompanied by Coq proofs of the lemmas extracted from CN. These are stored as follows: 

- Originating C file: `coq/working/EXAMPLENAME.c`
- Coq proof: `coq/working/EXAMPLENAME-build/Proof.v` 

See README in parent directory for directory organization details.

## Tools needed

To build the generated Coq lemmas, you will need to [download and
install Coq](https://coq.inria.fr/download).

## Batch build

To export and build lemmas for all examples just run

`../check.sh`. 

For each file in the `coq` folder, the script first
checks the CN verification and then exports lemmas to Coq and builds
the Coq files. When proofs are provided, those will be built too.

To provide proofs or test individual examples, see below.

## Testing individual examples

From this folder, to export lemmas from example `path/to/EXAMPLENAME.c`, do the following:

0. (optional) Check CN verification, without exporting lemmas, with

  `cn path/to/EXAMPLENAME.c`

1. Create a copy of the build folder with 

  `rsync -a ../coq-build/ path/to/EXAMPLENAME-build`
  
  (note trailing `/` after the first directory). This
  copies a template build folder that conveniently contains a
  `_CoqProject` file and the CN coq library `CN_Lib.v`. If the folder
  already exists, `rsync` just updates the files.
2. focus the lemmas with 
  
  `cn --lemmata=path/to/EXAMPLENAME-build/theories/ExportedLemmas.v path/to/EXAMPLENAME.c`
  
  This should create a new file
  `path/to/EXAMPLENAME-build/theories/ExportedLemmas.v` with all the
  exported types, definitions and lemmas from the file
  `path/to/EXAMPLENAME.c`.
3. Go to the build directory with 

  `pushd path/to/EXAMPLENAME-build`
  
  This will also store your current location to return later.
4. Create or update the Coq Makefile with 

  `coq_makefile -f _CoqProject -o Makefile.coq`
  
5. Build the Coq files with 

  `make -f Makefile.coq`
  
  This should create `*.vo` files for every `*.v` file in the
  `theories` directory.
6. Return to your starting folder with 

  `popd`

To add proofs, after running the steps above, create a file `Proofs.v`
in the `theories` folder, next to the generated
`ExportedLemmas.v`. The file must contain instances of the module
types defined in `ExportedLemmas.v`: `Parameters`, `Defs`, and
`Lemma_Spec` module type.

Your `theories/Proofs.v` file will look something like this:

```
Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.
Require Import CN_Lemmas.ExportedLemmas.


(*Parameters*)
Module ConcreteParameters <:Parameters.
(*Fill parameters here, if any*)
End ConcreteParameters.

(*Definitions*)
Module ConcreteDefs := Defs(ConcreteParameters).

Module ConcreteLemmaSpec <: Lemma_Spec(ConcreteParameters).
  Module D := ConcreteDefs.
  Import D.

  (*Prove the lemmas, if any. *)
  Definition example_lemma : example_lemma_type.
  Proof. (*Add here the proof*) . Qed.
  
End ConcreteLemmaSpec.
```

Once all the proofs have been completed in `Proofs.v`, repeat steps
3-6 above to build all files. If `Proofs.vo` is generated correctly,
the extracted lemmas have been proven.
