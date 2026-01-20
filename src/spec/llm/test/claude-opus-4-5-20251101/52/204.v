Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (-200 :: 300 :: 8000000 :: -400 :: -600 :: 300 :: nil) 1001 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (H8M: In 8000000 (-200 :: 300 :: 8000000 :: -400 :: -600 :: 300 :: nil)).
    { simpl. right. right. left. reflexivity. }
    specialize (H 8000000 H8M).
    lia.
Qed.