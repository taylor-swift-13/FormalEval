Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1000%Z; 500%Z; 250%Z; 6000000%Z; 62%Z; 31%Z] 2000%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (HIn : In 6000000%Z [1000%Z; 500%Z; 250%Z; 6000000%Z; 62%Z; 31%Z]).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 6000000%Z HIn).
    lia.
Qed.