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

Lemma test_find_zero_spec_aux : find_zero_spec [-8; -2; 1; 10; 6; 2] (0.8199922739620269).
Proof.
  unfold find_zero_spec.
  intros.
  admit.
Admitted.

Example test_find_zero_spec : find_zero_spec [-8; -2; 1; 10; 6; 2] (0.8199922739620269).
Proof.
  apply test_find_zero_spec_aux.
Qed.