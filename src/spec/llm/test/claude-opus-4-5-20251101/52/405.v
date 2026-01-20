Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (10000000 :: 9000000 :: 8000000 :: 2000 :: 6000000 :: 100 :: 8000000 :: nil) (-50) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 100 (10000000 :: 9000000 :: 8000000 :: 2000 :: 6000000 :: 100 :: 8000000 :: nil)) as Hin.
    { simpl. right. right. right. right. right. left. reflexivity. }
    specialize (H 100 Hin).
    lia.
Qed.