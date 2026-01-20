Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-3.4; 5.6; 15.4; -9.0; 10.1] 15.4.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 15.4 is in the list [-3.4; 5.6; 15.4; -9.0; 10.1] *)
    simpl.
    right. right. left. reflexivity.
  - (* Part 2: Prove for all x in [-3.4; 5.6; 15.4; -9.0; 10.1], x <= 15.4 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H *)
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + (* Case x = -3.4 *)
      subst. lra.
    + (* Case x = 5.6 *)
      subst. lra.
    + (* Case x = 15.4 *)
      subst. lra.
    + (* Case x = -9.0 *)
      subst. lra.
    + (* Case x = 10.1 *)
      subst. lra.
    + (* Case False (end of list) *)
      contradiction.
Qed.