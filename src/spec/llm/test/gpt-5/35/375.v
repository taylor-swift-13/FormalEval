Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec
    [12.377301343805572%R; 1.6651177816249232%R; -4.430953128389664%R; -3.4%R; 11.754416969860902%R; 5.6%R; 10.889126081885%R; 10.1%R; 12.377301343805572%R]
    12.377301343805572%R.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; subst; lra.
Qed.