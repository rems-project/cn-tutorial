(* theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.


Module Types.

  (* no type definitions required *)

End Types.


Module Type Parameters.
  Import Types.

  (* no parameters required *)

End Parameters.


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.


  Definition lem_trivial_type : Prop :=
    Is_true true.

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter lem_trivial : lem_trivial_type.

End Lemma_Spec.


