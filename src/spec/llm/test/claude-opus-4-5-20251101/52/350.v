Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (100 :: 200 :: 300 :: 100 :: nil) 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (Hin : In 100 (100 :: 200 :: 300 :: 100 :: nil)).
    { simpl. left. reflexivity. }
    specialize (H 100 Hin).
    lia.
Qed.