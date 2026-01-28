Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [7%Z; -2%Z; -3%Z; -3%Z; -4%Z] 0%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (H_contra : 7 < 0).
    {
      apply H.
      simpl.
      left.
      reflexivity.
    }
    lia.
Qed.