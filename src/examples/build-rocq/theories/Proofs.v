(* build-rocq/theories/ExportedDefinitions.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.
Require Import CN_Lemmas.ExportedDefinitions.


Module MyParams: Parameters.
End MyParams.

Module MyProofs : Lemma_Spec (MyParams).
  
  Module D := Defs(MyParams).
  Import D.

  Lemma append_nil_r : append_nil_r_type.
  Proof.
    intros l; induction l.
    - reflexivity.
    - simpl; rewrite IHl; reflexivity.
  Qed.
      
  Lemma append_cons_r : append_cons_r_type.
  Proof.
    intros l; induction l.
    - reflexivity.
    - intros; simpl; rewrite IHl; reflexivity.
  Qed.

End MyProofs.

