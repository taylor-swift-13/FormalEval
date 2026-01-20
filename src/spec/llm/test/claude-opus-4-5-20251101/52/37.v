Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (3 :: 1 :: 4 :: 7 :: 10 :: 7 :: nil) 6 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (H7 : In 7 (3 :: 1 :: 4 :: 7 :: 10 :: 7 :: nil)).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 7 H7).
    lia.
Qed.