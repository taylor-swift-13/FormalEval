Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (6.2 :: nil) (-201) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    assert (Hin : In 6.2 (6.2 :: nil)).
    { simpl. left. reflexivity. }
    specialize (H 6.2 Hin).
    lra.
Qed.