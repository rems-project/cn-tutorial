Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.
Require Import CN_Lemmas.ExportedLemmas.


(*Parameters*)
Module ConcreteParameters <:Parameters.
End ConcreteParameters.

(*Definitions*)
Module ConcreteDefs := Defs(ConcreteParameters).

Module ConcreteLemmaSpec <: Lemma_Spec(ConcreteParameters).
  Module D := ConcreteDefs.
  Import D.

  Definition lem_ineq : lem_ineq_type.
  Proof. unfold lem_ineq_type.
         constructor; assumption.
  Qed.
  
End ConcreteLemmaSpec.

