Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1 :: 4 :: 7 :: 9 :: nil) 6 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 7 (1 :: 4 :: 7 :: 9 :: nil)) as H7.
    { simpl. right. right. left. reflexivity. }
    specialize (H 7 H7).
    lia.
Qed.