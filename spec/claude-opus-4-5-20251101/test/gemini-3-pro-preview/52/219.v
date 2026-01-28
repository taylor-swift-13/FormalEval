Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [10%Z; -400%Z; 20%Z; -30%Z; 40%Z; 499%Z] 40%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (HIn : In 40%Z [10%Z; -400%Z; 20%Z; -30%Z; 40%Z; 499%Z]).
    { simpl. right. right. right. right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.