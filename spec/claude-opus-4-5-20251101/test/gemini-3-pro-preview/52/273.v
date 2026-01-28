Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1000%Z; 500%Z; 250%Z; 125%Z; 6%Z; 62%Z; 31%Z; 31%Z] 499%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 1000%Z).
    assert (In 1000%Z [1000%Z; 500%Z; 250%Z; 125%Z; 6%Z; 62%Z; 31%Z; 31%Z]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
Qed.