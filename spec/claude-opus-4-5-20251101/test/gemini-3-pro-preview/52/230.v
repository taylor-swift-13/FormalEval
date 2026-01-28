Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [9%Z; 20%Z; 2000%Z; 40%Z; -50%Z] 499%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 2000%Z).
    assert (HIn : In 2000%Z [9%Z; 20%Z; 2000%Z; 40%Z; -50%Z]).
    { simpl. right. right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.