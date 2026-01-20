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

Definition approx_zero_spec (xs : list R) (root : R) (eps : R) : Prop :=
  (exists n : nat, length xs = 2 * n /\ n > 0)%nat /\
  (last xs 0 <> 0) /\
  Rabs (poly xs root) < eps.

Example test_find_zero : approx_zero_spec [-4; 10; -2; 6; 5; -2] (0.3859218130812834) (0.0001).
Proof.
  unfold approx_zero_spec.
  split.
  - exists 3%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + simpl. unfold Rabs.
      destruct (Rcase_abs _); lra.
Qed.