Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rpower.
Require Import Lia.
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

Example find_zero_test :
  find_zero_spec [IZR (-10%Z); IZR (-2%Z)] (-5.0%R).
Proof.
  unfold find_zero_spec.
  split.
  - exists 1%nat. split; [simpl; lia | lia].
  - split.
    + simpl. apply Rlt_not_eq. lra.
    + simpl. lra.
Qed.