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

Example test_find_zero_spec : find_zero_spec [-3; -2; 3; 1935360001; 9449999; -3; 5; -6; 37; 3; -630001; -630000; -8; 9; -10; 3; -10; 9] 0.0011576141609444814.
Proof.
  unfold find_zero_spec.
  intros _ _.
  admit.
Admitted.