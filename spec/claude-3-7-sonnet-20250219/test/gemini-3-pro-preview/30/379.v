Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [1; 7; 3; -4; -5; 0; 6; -9; -5; 10; -9] [1; 7; 3; 6; 10].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]]; subst.
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
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]; subst.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + lia.
    + lia.
    + lia.
    + simpl; tauto.
    + lia.
    + lia.
    + simpl; tauto.
    + lia.
    + contradiction.
Qed.