Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [-200%Z; 10%Z; 20%Z; -30%Z; 40%Z; 8000000%Z; -50%Z] 8000000%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 8000000%Z).
    assert (H_in : In 8000000%Z [-200%Z; 10%Z; 20%Z; -30%Z; 40%Z; 8000000%Z; -50%Z]).
    { simpl. right. right. right. right. right. left. reflexivity. }
    apply H in H_in.
    lia.
Qed.