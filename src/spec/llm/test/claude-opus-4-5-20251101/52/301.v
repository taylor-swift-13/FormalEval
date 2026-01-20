Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (10000000 :: 9000000 :: 10000001 :: 10 :: 8000000 :: 6000000 :: 2000000 :: 10000001 :: 10000000 :: nil) 10 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    assert (In 10000000 (10000000 :: 9000000 :: 10000001 :: 10 :: 8000000 :: 6000000 :: 2000000 :: 10000001 :: 10000000 :: nil)) as Hin.
    { simpl. left. reflexivity. }
    specialize (H 10000000 Hin).
    lia.
Qed.