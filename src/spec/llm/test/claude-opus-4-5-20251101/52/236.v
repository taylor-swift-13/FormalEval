Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (100 :: 2000000 :: 10000002 :: 500 :: 8000002 :: nil) 8000000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 10000002 (100 :: 2000000 :: 10000002 :: 500 :: 8000002 :: nil)) as Hin.
    { simpl. right. right. left. reflexivity. }
    specialize (H 10000002 Hin).
    lia.
Qed.