Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rpower.
Require Import Lia.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (root : R) : Prop :=
  (exists n : nat, length xs = 2 * n /\ n > 0)%nat /\
  (last xs 0 <> 0) /\
  poly xs root = 0.

Definition approximately_zero (r : R) (epsilon : R) : Prop :=
  Rabs r < epsilon.

Definition find_zero_spec_approx (xs : list R) (root : R) (epsilon : R) : Prop :=
  (exists n : nat, length xs = 2 * n /\ n > 0)%nat /\
  (last xs 0 <> 0) /\
  approximately_zero (poly xs root) epsilon.

Example test_find_zero : find_zero_spec_approx [-2; -9; 3; -10] (-0.2000001230542504) 0.0001.
Proof.
  unfold find_zero_spec_approx.
  split.
  - exists 2%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + unfold approximately_zero.
      simpl.
      unfold Rabs.
      destruct (Rcase_abs _); lra.
Qed.