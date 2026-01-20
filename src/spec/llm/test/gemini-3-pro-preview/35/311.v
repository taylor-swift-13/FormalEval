Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; -50.04662603741016; 5.6; 15.4; -8.601314347821834; 10.1] 15.4.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 5 right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; try (subst; lra); try contradiction.
Qed.