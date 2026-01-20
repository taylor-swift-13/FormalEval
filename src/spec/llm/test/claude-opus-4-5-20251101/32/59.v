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

Definition find_zero_spec (xs : list R) (root : R) (epsilon : R) : Prop :=
  (exists n : nat, length xs = 2 * n /\ n > 0)%nat /\
  (last xs 0 <> 0) /\
  Rabs (poly xs root) < epsilon.

Example test_find_zero : find_zero_spec [6; -2; -6; 1] (0.9066403799501622) (0.0001).
Proof.
  unfold find_zero_spec.
  split.
  - exists 2%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + simpl. unfold Rabs.
      destruct (Rcase_abs _); lra.
Qed.