Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1 :: 3 :: 4 :: nil) 2 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 3 (1 :: 3 :: 4 :: nil)) as H3.
    { simpl. right. left. reflexivity. }
    specialize (H 3 H3).
    lia.
Qed.