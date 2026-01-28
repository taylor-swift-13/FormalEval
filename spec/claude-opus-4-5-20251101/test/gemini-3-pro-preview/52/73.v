Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1%Z; 2%Z; -5%Z; -4%Z; 4%Z] 4%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 4%Z).
    assert (In 4%Z [1%Z; 2%Z; -5%Z; -4%Z; 4%Z]).
    { simpl. right. right. right. right. left. reflexivity. }
    apply H in H0.
    lia.
Qed.