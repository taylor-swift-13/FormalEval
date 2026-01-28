Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100%Z; 9999999%Z; -400%Z] 8000001%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 9999999%Z).
    simpl in H.
    assert (9999999 < 8000001)%Z.
    {
      apply H.
      right. left. reflexivity.
    }
    lia.
Qed.