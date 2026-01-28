Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [5; 9; -3; -6; 2; 3; 8; 1; -4; 2] [5; 9; 2; 3; 8; 1; 2].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + contradiction.
  - intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]; subst.
    + simpl; tauto.
    + simpl; tauto.
    + lia.
    + lia.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + lia.
    + simpl; tauto.
    + contradiction.
Qed.