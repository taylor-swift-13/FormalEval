Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [1.2%R; -1.7653933945886042%R; 1.2%R; -3.4%R; -9.0%R; 10.1%R; -3.4%R] 10.1%R.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. right. right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; subst; lra.
Qed.