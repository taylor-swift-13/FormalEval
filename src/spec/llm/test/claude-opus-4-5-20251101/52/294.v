Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (100 :: 9999999 :: (-400) :: nil) 8000001 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (H1: In 9999999 (100 :: 9999999 :: (-400) :: nil)).
    { simpl. right. left. reflexivity. }
    specialize (H 9999999 H1).
    lia.
Qed.