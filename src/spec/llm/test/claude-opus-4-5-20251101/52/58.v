Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1 :: 2 :: 5 :: 3 :: 4 :: nil) 4 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 5 (1 :: 2 :: 5 :: 3 :: 4 :: nil)) as Hin.
    { simpl. right. right. left. reflexivity. }
    specialize (H 5 Hin).
    lia.
Qed.