Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -3.4; 81.6; 1.2; -3.4; 5.6; 15.645230325881018; -9.0; 10.1] 81.6.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
Qed.