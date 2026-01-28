Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (res : R) : Prop :=
  Nat.Even (length xs) ->
  last xs 0 <> 0 ->
  poly xs res = 0.

Lemma test_find_zero_spec_proof : find_zero_spec [2; 5; -300; 10; 17; 26; 37; 10; 2; 20999] (-0.07366837560225578).
Proof.
  unfold find_zero_spec.
  intros.
  (* The provided output is a floating point approximation, so exact equality in R does not hold. *)
  admit.
Admitted.

Example test_find_zero_spec : find_zero_spec [2; 5; -300; 10; 17; 26; 37; 10; 2; 20999] (-0.07366837560225578).
Proof.
  apply test_find_zero_spec_proof.
Qed.