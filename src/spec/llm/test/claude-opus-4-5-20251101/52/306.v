Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (6 :: 2 :: 6 :: 8 :: nil) (-30) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    assert (Hin : In 6 (6 :: 2 :: 6 :: 8 :: nil)).
    { simpl. left. reflexivity. }
    specialize (H 6 Hin).
    lia.
Qed.