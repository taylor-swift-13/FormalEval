Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lra.
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
  Rabs (poly xs res) < 1.

Example test_find_zero_spec : find_zero_spec [-6; 21000; 3; 2; 8; -4; 26; 6; 5; -1; 1935360000; 26] 0.00028571428571428574.
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  lra.
Qed.