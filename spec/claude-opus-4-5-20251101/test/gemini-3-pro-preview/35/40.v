Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (result : R) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [1.5; 3; 2; -4; -3.5; 0] 3.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    right; left.
    reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]]; subst.
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + contradiction.
Qed.