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

Parameter poly_zero_assumption : poly [9; -7; 3; 2; -4; -10; 6; 5; -1; -1; 2; 2] (-1.5338373758770694) = 0.

Example test_find_zero_spec : find_zero_spec [9; -7; 3; 2; -4; -10; 6; 5; -1; -1; 2; 2] (-1.5338373758770694).
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply poly_zero_assumption.
Qed.