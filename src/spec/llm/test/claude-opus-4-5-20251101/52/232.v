Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (-200 :: 10 :: 20 :: -30 :: 40 :: 8000000 :: -50 :: nil) 8000000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (Hin: In 8000000 (-200 :: 10 :: 20 :: -30 :: 40 :: 8000000 :: -50 :: nil)).
    { simpl. right. right. right. right. right. left. reflexivity. }
    specialize (H 8000000 Hin).
    lia.
Qed.