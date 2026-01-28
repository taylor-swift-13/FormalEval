Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [-200%Z; 300%Z; 8000000%Z; -400%Z; -600%Z; 300%Z; 300%Z] 125%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    specialize (H 300%Z).
    assert (In 300%Z [-200%Z; 300%Z; 8000000%Z; -400%Z; -600%Z; 300%Z; 300%Z]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lia.
Qed.