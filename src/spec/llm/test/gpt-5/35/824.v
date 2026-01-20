Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [1.2%R; -4.5%R; -3.4%R; 2.929311287687052%R; 7.8%R; -10.492535520433075%R; 2.3356007610251286%R; -9.0%R; 11.838575197213943%R; -4.5%R] 11.838575197213943%R.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. right. right. right. right. right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]; subst; lra.
Qed.