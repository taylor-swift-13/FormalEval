Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; 15.4; -9.0; 93.8] 93.8.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 93.8 is in the list *)
    simpl.
    right. right. right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 93.8 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* Case x = 1.2 *)
      subst. lra.
    + (* Case x = -4.5 *)
      subst. lra.
    + (* Case x = -3.4 *)
      subst. lra.
    + (* Case x = 15.4 *)
      subst. lra.
    + (* Case x = -9.0 *)
      subst. lra.
    + (* Case x = 93.8 *)
      subst. lra.
    + (* Case False *)
      contradiction.
Qed.