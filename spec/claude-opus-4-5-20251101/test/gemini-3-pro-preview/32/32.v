Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rpower.
Require Import Psatz.
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

Parameter poly_root_approx : poly [5; 7; -5; -2] (-0.5472144844465354) = 0.

Example find_zero_example : find_zero_spec [5; 7; -5; -2] (-0.5472144844465354).
Proof.
  unfold find_zero_spec.
  split.
  - exists 2%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + apply poly_root_approx.
Qed.