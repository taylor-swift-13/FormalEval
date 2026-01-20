Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1000 :: 500 :: 250 :: 6000000 :: nil) 2000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    assert (H1: In 6000000 (1000 :: 500 :: 250 :: 6000000 :: nil)).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 6000000 H1).
    lia.
Qed.