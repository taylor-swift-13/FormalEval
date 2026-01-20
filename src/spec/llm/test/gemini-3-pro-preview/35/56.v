Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [3; 6; -3.5; 0] 6.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 6 is in the list [3; 6; -3.5; 0] *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in [3; 6; -3.5; 0], x <= 6 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]].
    + (* Case x = 3 *)
      subst. lra.
    + (* Case x = 6 *)
      subst. lra.
    + (* Case x = -3.5 *)
      subst. lra.
    + (* Case x = 0 *)
      subst. lra.
    + (* Case False *)
      contradiction.
Qed.