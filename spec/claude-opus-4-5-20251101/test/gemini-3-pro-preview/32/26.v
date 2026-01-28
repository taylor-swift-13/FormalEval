Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rpower.
Require Import Psatz. (* Required for lra and lia tactics *)
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

Example find_zero_example : find_zero_spec [-10; -2; 6; -5; 6; -7; 10; -1] (-0.7015198788268473).
Proof.
  unfold find_zero_spec.
  split.
  - exists 4%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + admit.
Admitted.