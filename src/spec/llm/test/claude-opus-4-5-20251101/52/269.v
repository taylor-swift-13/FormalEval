Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (10 :: 20 :: (-30) :: 40 :: 500 :: 20 :: nil) 126 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (Hin : In 500 (10 :: 20 :: (-30) :: 40 :: 500 :: 20 :: nil)).
    { simpl. right. right. right. right. left. reflexivity. }
    specialize (H 500 Hin).
    lia.
Qed.