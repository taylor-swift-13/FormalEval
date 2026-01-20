Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (-5 :: 10 :: -3 :: 1 :: nil) 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    assert (H10: In 10 (-5 :: 10 :: -3 :: 1 :: nil)).
    { simpl. right. left. reflexivity. }
    specialize (H 10 H10).
    lia.
Qed.