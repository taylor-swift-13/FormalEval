Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-1; -2; -5; -3; -4; 6; 0; 6; 7; -9; 10; 5] [6; 6; 7; 10; 5].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]]; subst; try contradiction.
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
    + split; [simpl; tauto | lia].
  - intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [HIn | [HIn | [HIn | [HIn | [HIn | [HIn | [HIn | [HIn | [HIn | [HIn | [HIn | [HIn | HIn]]]]]]]]]]]]; subst; try contradiction.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + simpl; tauto.
    + lia.
    + simpl; tauto.
    + simpl; tauto.
    + lia.
    + simpl; tauto.
    + simpl; tauto.
Qed.