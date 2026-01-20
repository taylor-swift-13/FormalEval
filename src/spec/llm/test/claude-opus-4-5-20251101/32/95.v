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

Definition approximately_zero (r : R) (eps : R) : Prop :=
  Rabs r < eps.

Definition find_zero_spec_approx (xs : list R) (root : R) (eps : R) : Prop :=
  (exists n : nat, length xs = 2 * n /\ n > 0)%nat /\
  (last xs 0 <> 0) /\
  approximately_zero (poly xs root) eps.

Example test_find_zero : find_zero_spec_approx [4; 9; 6; 3; 7; 4] (-1.4282609139932103) (1/1000).
Proof.
  unfold find_zero_spec_approx.
  split.
  - exists 3%nat.
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