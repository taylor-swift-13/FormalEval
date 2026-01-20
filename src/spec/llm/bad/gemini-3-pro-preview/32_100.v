Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Micromega.Lra.
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
  Rabs (poly xs res) < 1 / 1000.

Example test_find_zero_spec : find_zero_spec [5; 10; -3; 1] (-0.4350015266201541).
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  unfold Rabs.
  destruct (Rcase_abs _); lra.
Qed.