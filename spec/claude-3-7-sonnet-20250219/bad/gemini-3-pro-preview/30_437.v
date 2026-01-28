Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition get_positive_spec (l: list R) (res: list R) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec 
  [0.5; -4; 2.5; 5; -8; -4; -7; -11.18889279027017; -10.5; 2.5] 
  [0.5; 2.5; 5; 2.5].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]]; subst.
    + (* x = 0.5 *)
      split.
      * simpl; tauto.
      * lra.
    + (* x = 2.5 *)
      split.
      * simpl; tauto.
      * lra.
    + (* x = 5 *)
      split.
      * simpl; tauto.
      * lra.
    + (* x = 2.5 *)
      split.
      * simpl; tauto.
      * lra.
    + (* Empty tail *)
      contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]; subst.
    + (* x = 0.5 *)
      simpl; tauto.
    + (* x = -4 *)
      lra.
    + (* x = 2.5 *)
      simpl; tauto.
    + (* x = 5 *)
      simpl; tauto.
    + (* x = -8 *)
      lra.
    + (* x = -4 *)
      lra.
    + (* x = -7 *)
      lra.
    + (* x = -11.18... *)
      lra.
    + (* x = -10.5 *)
      lra.
    + (* x = 2.5 *)
      simpl; tauto.
    + (* Empty tail *)
      contradiction.
Qed.