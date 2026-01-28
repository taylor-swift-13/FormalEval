Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [-4%Z; -3%Z; -2%Z; -1%Z] (-1)%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (HIn : In (-1) [-4; -3; -2; -1]).
    { simpl. do 3 right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.