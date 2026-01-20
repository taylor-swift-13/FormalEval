Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1 :: 3 :: 10 :: 4 :: nil) 5 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (H10 : In 10 (1 :: 3 :: 10 :: 4 :: nil)).
    { simpl. right. right. left. reflexivity. }
    specialize (H 10 H10).
    lia.
Qed.