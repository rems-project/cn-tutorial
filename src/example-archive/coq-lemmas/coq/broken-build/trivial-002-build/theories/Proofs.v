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

  Definition lem_impossible_in_coq : lem_impossible_in_coq_type.
  Proof. unfold lem_impossible_in_coq_type.
         (* Goal: forall x : Z, x <= 4294967295*)
         (* That's impossible to prove! *)
  Abort. Qed.
  
End ConcreteLemmaSpec.

