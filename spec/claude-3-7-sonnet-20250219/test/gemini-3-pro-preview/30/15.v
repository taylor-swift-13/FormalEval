Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [10; -10; 15; -3; 20; -20; 25; -25] [10; 15; 20; 25].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]]; subst.
    + (* x = 10 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 15 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 20 *)
      split.
      * simpl; tauto.
      * lia.
    + (* x = 25 *)
      split.
      * simpl; tauto.
      * lia.
    + (* Empty tail *)
      contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; subst.
    + (* x = 10 *)
      simpl; tauto.
    + (* x = -10 *)
      lia.
    + (* x = 15 *)
      simpl; tauto.
    + (* x = -3 *)
      lia.
    + (* x = 20 *)
      simpl; tauto.
    + (* x = -20 *)
      lia.
    + (* x = 25 *)
      simpl; tauto.
    + (* x = -25 *)
      lia.
    + (* Empty tail *)
      contradiction.
Qed.