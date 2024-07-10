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

  Definition lem_impossible_in_Coq : lem_impossible_in_Coq_type.
  Proof. unfold lem_impossible_in_Coq_type.
         (* Goal: forall x : Z,
            CN_Lib.wrapI 0 4294967295
             (CN_Lib.wrapI 0 4294967295 (x + 1) - 1) = x *)
         (* That's impossible to prove! The LHS is always in bound,
            but x can be any Z *)
  Abort. Qed.
         
End ConcreteLemmaSpec.

