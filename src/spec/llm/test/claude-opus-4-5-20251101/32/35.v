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

Definition root := 0.6355658373975246.

Example test_find_zero : find_zero_spec [8; -3; -10; -8] root.
Proof.
  unfold find_zero_spec.
  split.
  - exists 2%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + unfold poly, root.
      Admitted.