## Examples

CN examples using lemmas that can be extracted to Coq. The examples
are split into:

- Trivial
- Recursive (Not yet handled by the export)

## Generating Coq Lemmas 

To generate Coq lemma for a given `example-file.c` run

```
cn --lemmata=build/theories/ExportedLemmas.v example-file.c
```

File `build/theories/ExportedLemmas.v` should be generated with the
right definitions. Each lemma is exported as a new definition and then
added as a parameter in the module named `Lemma_Spec`. It should look
something like this

```

Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.


  Definition my_lemma_type : Prop :=
    Is_true true.

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter my_lemma : my_lemma_type.

End Lemma_Spec.
```

## Proving the Coq Lemmas

To prove the lemmas, instantiate a new module with type `Lemma_Spec`
containing each of parameters as lemmas and their proofs. For the
example above, the proofs look like this

```

Module MyP: Parameters.
End MyP.

Module Proofs : Lemma_Spec MyP.
  Module D := Defs(MyP).
  Import D.

  Lemma  just_arith2 : my_lemma_type.
  Proof.
    solve [hnf; trivial].
  Qed.

End Proofs.
  
```
