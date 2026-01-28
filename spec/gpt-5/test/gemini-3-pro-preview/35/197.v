Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; 5.6; 15.4; -9.0; 10.1; 15.4] 15.4.
Proof.
  unfold max_element_spec.
  repeat split.
  -
    discriminate.
  -
    simpl.
    right. right. right. right. left. reflexivity.
  -
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
Qed.