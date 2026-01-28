Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [1; 1; 1; -8; 1; 1; 11; 2; 2; 2; 2; 2; 2] [1; 1; 1; 1; 1; 11; 2; 2; 2; 2; 2; 2].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]; subst.
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + contradiction.
  - intros x H HPos.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]]; subst.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + lia.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + contradiction.
Qed.