Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; -25.6; -9.0; 1.2; 1.2; -4.5] 1.2.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 1.2 is in the list *)
    simpl.
    left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= 1.2 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H for list of length 8 *)
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
    + (* Case x = 1.2 *)
      subst. lra.
    + (* Case x = -4.5 *)
      subst. lra.
    + (* Case x = -3.4 *)
      subst. lra.
    + (* Case x = -25.6 *)
      subst. lra.
    + (* Case x = -9.0 *)
      subst. lra.
    + (* Case x = 1.2 *)
      subst. lra.
    + (* Case x = 1.2 *)
      subst. lra.
    + (* Case x = -4.5 *)
      subst. lra.
    + (* Case False (end of list) *)
      contradiction.
Qed.