Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (0 :: -1 :: 0 :: 0 :: 0 :: nil) 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 0 (0 :: -1 :: 0 :: 0 :: 0 :: nil)) as H0.
    { simpl. left. reflexivity. }
    specialize (H 0 H0).
    lia.
Qed.