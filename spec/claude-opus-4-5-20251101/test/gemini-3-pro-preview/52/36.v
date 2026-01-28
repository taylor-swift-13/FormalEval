Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1%Z; 3%Z; 10%Z; 4%Z] 5%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    specialize (H 10%Z).
    assert (In 10%Z [1%Z; 3%Z; 10%Z; 4%Z]) as HIn.
    { simpl. right. right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.