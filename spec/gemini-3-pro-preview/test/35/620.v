Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; 57.2; -3.4; 5.6; 7.8; -9.0; 10.1; 5.6] 57.2.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 57.2 is in the list *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 57.2 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
    + (* Case x = 1.2 *)
      subst. lra.
    + (* Case x = 57.2 *)
      subst. lra.
    + (* Case x = -3.4 *)
      subst. lra.
    + (* Case x = 5.6 *)
      subst. lra.
    + (* Case x = 7.8 *)
      subst. lra.
    + (* Case x = -9.0 *)
      subst. lra.
    + (* Case x = 10.1 *)
      subst. lra.
    + (* Case x = 5.6 *)
      subst. lra.
    + (* Case False *)
      contradiction.
Qed.