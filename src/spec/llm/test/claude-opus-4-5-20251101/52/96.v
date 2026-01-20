Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (-4 :: -3 :: -2 :: 4 :: -2 :: nil) 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (H4: In 4 (-4 :: -3 :: -2 :: 4 :: -2 :: nil)).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 4 H4).
    lia.
Qed.