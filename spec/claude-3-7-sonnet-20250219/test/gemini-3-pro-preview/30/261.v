Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition get_positive_spec (l: list R) (res: list R) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [0.5; 0; 2.5; 5; -2.2; -8; -0.75; 7.7; 9.9; -10.5] [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]]; subst.
    + split.
      * simpl; tauto.
      * lra.
    + split.
      * simpl; tauto.
      * lra.
    + split.
      * simpl; tauto.
      * lra.
    + split.
      * simpl; tauto.
      * lra.
    + split.
      * simpl; tauto.
      * lra.
    + contradiction.
  - intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]; subst.
    + simpl; tauto.
    + lra.
    + simpl; tauto.
    + simpl; tauto.
    + lra.
    + lra.
    + lra.
    + simpl; tauto.
    + simpl; tauto.
    + lra.
    + contradiction.
Qed.