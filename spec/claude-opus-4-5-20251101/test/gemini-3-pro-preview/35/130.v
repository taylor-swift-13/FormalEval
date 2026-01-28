Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (result : R) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; -3.4; 5.6; 15.4; -9.0; 10.1; 10.1] 15.4.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    right; right; right; right; right; left.
    reflexivity.
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]; subst.
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + contradiction.
Qed.