Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1%Z; 2%Z; 5%Z; 3%Z; 4%Z] 4%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    assert (C: 5 < 4).
    { apply H. simpl. right. right. left. reflexivity. }
    lia.
Qed.