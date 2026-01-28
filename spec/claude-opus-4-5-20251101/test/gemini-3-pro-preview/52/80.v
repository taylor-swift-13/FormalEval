Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1%Z; 0%Z; 2%Z; 0%Z; 0%Z] 2%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (HIn : In 2 [1; 0; 2; 0; 0]).
    { simpl. right. right. left. reflexivity. }
    specialize (H 2 HIn).
    lia.
Qed.