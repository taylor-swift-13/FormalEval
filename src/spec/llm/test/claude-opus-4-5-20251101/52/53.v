Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (3.5 :: 2.2 :: 1.1 :: nil) (-4) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (Hin : In 3.5 (3.5 :: 2.2 :: 1.1 :: nil)).
    { simpl. left. reflexivity. }
    specialize (H 3.5 Hin).
    lra.
Qed.