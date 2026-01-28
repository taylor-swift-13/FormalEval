Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [1; 2; -3; -5; 0; 6; 7; -9; 10] [1; 2; 6; 7; 10].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]]; subst.
    + (* x = 1 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 2 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 6 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 7 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 10 *)
      split.
      * simpl; tauto.
      * lia.
    + (* Empty tail *)
      contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]; subst.
    + (* x = 1 *)
      simpl; tauto.
    + (* x = 2 *)
      simpl; tauto.
    + (* x = -3 *)
      lia.
    + (* x = -5 *)
      lia.
    + (* x = 0 *)
      lia.
    + (* x = 6 *)
      simpl; tauto.
    + (* x = 7 *)
      simpl; tauto.
    + (* x = -9 *)
      lia.
    + (* x = 10 *)
      simpl; tauto.
    + (* Empty tail *)
      contradiction.
Qed.