Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [30%Z; 97%Z; 90%Z; 59%Z] 0%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 30%Z).
    assert (In 30%Z [30%Z; 97%Z; 90%Z; 59%Z]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
Qed.