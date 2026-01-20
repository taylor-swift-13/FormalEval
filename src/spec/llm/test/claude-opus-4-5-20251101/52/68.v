Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (4 :: -4 :: 7 :: 10 :: -4 :: nil) 7 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 7 (4 :: -4 :: 7 :: 10 :: -4 :: nil)) as Hin.
    { simpl. right. right. left. reflexivity. }
    specialize (H 7 Hin).
    lia.
Qed.