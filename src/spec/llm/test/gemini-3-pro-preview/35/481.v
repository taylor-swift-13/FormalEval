Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; 69.4; -3.4; 77.07852302260174; 10.1; 1.2] 77.07852302260174.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove res is in the list *)
    simpl.
    right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= res *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
Qed.