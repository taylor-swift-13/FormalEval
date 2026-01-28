Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [7; 8; 11; 12; 15; 17; -1; 11] [7; 8; 11; 12; 15; 17; 11].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst.
    + (* x = 7 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 8 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 11 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 12 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 15 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 17 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 11 *)
      split.
      * simpl; tauto.
      * lia.
    + (* Empty tail *)
      contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; subst.
    + (* x = 7 *)
      simpl; tauto.
    + (* x = 8 *)
      simpl; tauto.
    + (* x = 11 *)
      simpl; tauto.
    + (* x = 12 *)
      simpl; tauto.
    + (* x = 15 *)
      simpl; tauto.
    + (* x = 17 *)
      simpl; tauto.
    + (* x = -1 *)
      lia.
    + (* x = 11 *)
      simpl; tauto.
    + (* Empty tail *)
      contradiction.
Qed.