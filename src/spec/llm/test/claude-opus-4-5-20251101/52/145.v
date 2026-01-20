Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (100 :: 250 :: 2000000 :: 300 :: (-400) :: 500 :: (-600) :: nil) 100 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In 100 (100 :: 250 :: 2000000 :: 300 :: (-400) :: 500 :: (-600) :: nil)) as Hin.
    { simpl. left. reflexivity. }
    specialize (H 100 Hin).
    lia.
Qed.