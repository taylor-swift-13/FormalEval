Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (10000001 :: -200 :: 300 :: -400 :: 500 :: -600 :: nil) 1999 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (Hin : In 10000001 (10000001 :: -200 :: 300 :: -400 :: 500 :: -600 :: nil)).
    { simpl. left. reflexivity. }
    specialize (H 10000001 Hin).
    lia.
Qed.