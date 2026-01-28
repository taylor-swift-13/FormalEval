Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Definition get_true_spec (l: list bool) (res: list bool) : Prop :=
  (forall x, In x res -> In x l /\ x = true) /\
  (forall x, In x l -> x = true -> In x res).

Example test_get_true : get_true_spec [false; true; false; false; true] [true; true].
Proof.
  unfold get_true_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | H]]; subst.
    + split.
      * simpl; tauto.
      * reflexivity.
    + split.
      * simpl; tauto.
      * reflexivity.
    + contradiction.
  - intros x HIn HTrue.
    subst.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | H]]]]].
    + discriminate.
    + simpl; tauto.
    + discriminate.
    + discriminate.
    + simpl; tauto.
    + contradiction.
Qed.