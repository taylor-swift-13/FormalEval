Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; 6.808256183253008; -3.4; 5.6; 7.8; -9.0; 10.1; 10.1] 10.1.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 10.1 is in the list *)
    simpl.
    do 6 right. left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= 10.1 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; subst; try lra; try contradiction.
Qed.