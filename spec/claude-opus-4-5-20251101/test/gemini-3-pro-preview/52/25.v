Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [-4%Z; -3%Z; -2%Z; 4%Z; -4%Z] (-1)%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (HIn : In 4%Z [-4%Z; -3%Z; -2%Z; 4%Z; -4%Z]).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 4%Z HIn).
    lia.
Qed.