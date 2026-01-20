Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (0 :: 0 :: 2 :: 0 :: 0 :: nil) 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 2 (0 :: 0 :: 2 :: 0 :: 0 :: nil)) as Hin.
    { simpl. right. right. left. reflexivity. }
    specialize (H 2 Hin).
    lia.
Qed.