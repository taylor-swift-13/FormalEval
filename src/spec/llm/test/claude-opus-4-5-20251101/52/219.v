Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (10 :: (-400) :: 20 :: (-30) :: 40 :: 499 :: nil) 40 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    assert (In 499 (10 :: (-400) :: 20 :: (-30) :: 40 :: 499 :: nil)) as Hin.
    { simpl. right. right. right. right. right. left. reflexivity. }
    specialize (H 499 Hin).
    lia.
Qed.