Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [1; -100; -5; 6; 7; 2; -100] [1; 6; 7; 2].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]]; subst.
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
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst.
    + simpl; tauto.
    + lia.
    + lia.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + lia.
    + contradiction.
Qed.