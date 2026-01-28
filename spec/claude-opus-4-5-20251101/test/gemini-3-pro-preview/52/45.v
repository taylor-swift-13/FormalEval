Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [0%Z; 0%Z; 2%Z; 0%Z; 0%Z] 1%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 2).
    assert (In 2 [0; 0; 2; 0; 0]) as HIn.
    { simpl. right. right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.