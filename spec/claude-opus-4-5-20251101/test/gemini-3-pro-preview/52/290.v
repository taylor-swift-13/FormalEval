Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [10%Z; 20%Z; -30%Z; 40%Z; 499%Z; -30%Z] 14%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    specialize (H 20%Z).
    assert (Hin: In 20%Z [10%Z; 20%Z; -30%Z; 40%Z; 499%Z; -30%Z]).
    { simpl. right. left. reflexivity. }
    apply H in Hin.
    lia.
Qed.