Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; -3.4%R; 1.2%R; -3.4%R; 5.6%R; -3.4%R; 17.742268880987826%R; -9.0%R; 11.393628605126539%R] 17.742268880987826%R.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove the result is in the list *)
    simpl.
    right. right. right. right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
    + (* Case x = 1.2 *)
      subst. lra.
    + (* Case x = -3.4 *)
      subst. lra.
    + (* Case x = 1.2 *)
      subst. lra.
    + (* Case x = -3.4 *)
      subst. lra.
    + (* Case x = 5.6 *)
      subst. lra.
    + (* Case x = -3.4 *)
      subst. lra.
    + (* Case x = 17.74... *)
      subst. lra.
    + (* Case x = -9.0 *)
      subst. lra.
    + (* Case x = 11.39... *)
      subst. lra.
    + (* Case False (end of list) *)
      contradiction.
Qed.