Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (10 :: 6000001 :: (-30) :: 40 :: (-50) :: nil) 13 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 6000001 (10 :: 6000001 :: (-30) :: 40 :: (-50) :: nil)) as Hin.
    { simpl. right. left. reflexivity. }
    specialize (H 6000001 Hin).
    lia.
Qed.