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

Example test_find_zero_spec : find_zero_spec [-2; -6; -9; -8; -25; -630002] (-0.07596281542152894).
Proof.
  unfold find_zero_spec.
  intros _ _.
  compute.
  lra.
Qed.