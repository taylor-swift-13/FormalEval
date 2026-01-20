Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec ((-400) :: 100 :: (-200) :: 300 :: (-400) :: 500 :: (-600) :: (-600) :: nil) 302 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 500 ((-400) :: 100 :: (-200) :: 300 :: (-400) :: 500 :: (-600) :: (-600) :: nil)) as Hin.
    { simpl. right. right. right. right. right. left. reflexivity. }
    specialize (H 500 Hin).
    lia.
Qed.