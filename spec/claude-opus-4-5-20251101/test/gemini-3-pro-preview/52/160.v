Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100%Z; 250%Z; 2000000%Z; 300%Z; -400%Z; 500%Z; -600%Z] 1999%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 2000000%Z).
    assert (In 2000000%Z [100%Z; 250%Z; 2000000%Z; 300%Z; -400%Z; 500%Z; -600%Z]).
    { simpl. right. right. left. reflexivity. }
    apply H in H0.
    lia.
Qed.