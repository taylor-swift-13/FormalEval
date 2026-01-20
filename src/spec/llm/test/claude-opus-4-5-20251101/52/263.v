Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (8000001 :: 1000 :: 9999998 :: 10000000 :: 9000000 :: 10 :: 9999999 :: 8000000 :: 7000000 :: 6000000 :: 2000000 :: 9999998 :: nil) 20 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 8000001 (8000001 :: 1000 :: 9999998 :: 10000000 :: 9000000 :: 10 :: 9999999 :: 8000000 :: 7000000 :: 6000000 :: 2000000 :: 9999998 :: nil)) as Hin.
    { simpl. left. reflexivity. }
    specialize (H 8000001 Hin).
    lia.
Qed.