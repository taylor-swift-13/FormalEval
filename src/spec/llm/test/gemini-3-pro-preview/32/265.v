Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
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

Example test_find_zero_spec : find_zero_spec [1; -2; 4; -4; 5; -6; 7; 9; -11; -4] 0.9652944878329875%R.
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  unfold Rabs.
  match goal with |- context [Rcase_abs ?x] => destruct (Rcase_abs x) end; lra.
Qed.