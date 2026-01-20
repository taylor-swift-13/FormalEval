Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; 5.6; 7.8; 1.9737820350258957; -9.0; 11.838575197213943] 11.838575197213943.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove max is in the list *)
    simpl.
    right. right. right. right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= max *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H *)
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
Qed.