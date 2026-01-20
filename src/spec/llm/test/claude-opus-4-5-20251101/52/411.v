Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1000 :: 500 :: 250 :: 62 :: 30 :: 62 :: nil) 200 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    assert (H1000 : In 1000 (1000 :: 500 :: 250 :: 62 :: 30 :: 62 :: nil)).
    { simpl. left. reflexivity. }
    specialize (H 1000 H1000).
    lia.
Qed.