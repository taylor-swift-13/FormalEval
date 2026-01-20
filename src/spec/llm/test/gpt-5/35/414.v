Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [88.15713024897141%R; -11.39330787369553%R; 10.675343474768061%R; 10.675343474768061%R] 88.15713024897141%R.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|[H|[H|[H|[]]]]]; subst; lra.
Qed.