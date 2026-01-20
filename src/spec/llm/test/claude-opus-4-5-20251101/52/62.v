Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (2 :: 4 :: 6 :: 8 :: nil) 6 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (H6 : In 6 (2 :: 4 :: 6 :: 8 :: nil)).
    { simpl. right. right. left. reflexivity. }
    specialize (H 6 H6).
    lia.
Qed.