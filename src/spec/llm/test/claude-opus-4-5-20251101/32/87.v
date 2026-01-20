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

Definition root_approx : R := 2.018535319876459.

Axiom poly_at_root_approx : poly [8; 9; 10; 1; 4; 4; 4; -4] root_approx = 0.

Example test_find_zero : find_zero_spec [8; 9; 10; 1; 4; 4; 4; -4] root_approx.
Proof.
  unfold find_zero_spec.
  split.
  - exists 4%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + exact poly_at_root_approx.
Qed.