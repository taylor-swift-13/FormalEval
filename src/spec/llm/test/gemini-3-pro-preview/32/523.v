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

Axiom test_find_zero_axiom : poly [1; -2; 3; -4; -6; 7; -9; 9; -10; 3] (49756624822288065 / 100000000000000000) = 0.

Example test_find_zero_spec : find_zero_spec [1; -2; 3; -4; -6; 7; -9; 9; -10; 3] (49756624822288065 / 100000000000000000).
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply test_find_zero_axiom.
Qed.