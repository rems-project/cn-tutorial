(* build-rocq/theories/ExportedDefinitions.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.


Module Types.

  Inductive
    seq : Type :=
    | Seq_Nil : seq
    | Seq_Cons : Z -> seq -> seq.

End Types.


Module Type Parameters.
  Import Types.

  (* no parameters required *)

End Parameters.


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.

  Fixpoint append (xs : seq) (ys : seq) :=
    (match xs with | (Seq_Nil) => ys | (Seq_Cons h zs) => (Seq_Cons h (append zs ys)) end).

  Fixpoint snoc (xs : seq) (y : Z) :=
    (match xs with | (Seq_Nil) => (Seq_Cons y (Seq_Nil)) | (Seq_Cons x zs) => (Seq_Cons x (snoc zs y)) end).

  Definition append_nil_r_type : Prop :=
    forall (l1 : seq),


((append l1 (Seq_Nil)) = l1).

  Definition append_cons_r_type : Prop :=
    forall (l1 : seq),

forall (x : Z),

forall (l2 : seq),


((append l1 (Seq_Cons x l2)) = (append (snoc l1 x) l2)).

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter append_nil_r : append_nil_r_type.

  Parameter append_cons_r : append_cons_r_type.

End Lemma_Spec.
