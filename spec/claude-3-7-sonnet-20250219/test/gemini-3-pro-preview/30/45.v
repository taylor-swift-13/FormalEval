Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [5; 9; -6; 2; 3; 8; 0] [5; 9; 2; 3; 8].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]]; subst.
    + (* x = 5 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 9 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 2 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 3 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 8 *)
      split.
      * simpl; tauto.
      * lia.
    + (* Empty tail *)
      contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst.
    + (* x = 5 *)
      simpl; tauto.
    + (* x = 9 *)
      simpl; tauto.
    + (* x = -6 *)
      lia.
    + (* x = 2 *)
      simpl; tauto.
    + (* x = 3 *)
      simpl; tauto.
    + (* x = 8 *)
      simpl; tauto.
    + (* x = 0 *)
      lia.
    + (* Empty tail *)
      contradiction.
Qed.