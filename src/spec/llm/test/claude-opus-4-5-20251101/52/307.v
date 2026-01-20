Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec ((-200) :: 300 :: 8000000 :: (-400) :: (-600) :: 300 :: (-200) :: nil) 100 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 300 ((-200) :: 300 :: 8000000 :: (-400) :: (-600) :: 300 :: (-200) :: nil)) as Hin.
    { simpl. right. left. reflexivity. }
    specialize (H 300 Hin).
    lia.
Qed.