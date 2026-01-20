Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec
    [1.2%R; -4.5%R; -3.4%R; 5.6%R; 7.8%R; -9.0%R; 10.1%R; -12.3%R; 15.4%R; 20.5%R; -25.6%R; 30.7%R; 7.8%R; -35.8%R; 40.9%R; -46.0%R; 51.1%R; 57.2%R; -63.3%R; 69.4%R; -75.5%R; 81.6%R; -87.7%R; -8.601314347821834%R; 93.8%R; 99.9%R; -25.6%R]
    99.9%R.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. do 25 right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H
      |[H|[]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst; lra.
Qed.