Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [8000001%Z; 1000%Z; 9999998%Z; 10000000%Z; 9000000%Z; 10%Z; 9999999%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z; 9999998%Z] 20%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (8000001 < 20)%Z.
    { apply H. simpl. left. reflexivity. }
    lia.
Qed.