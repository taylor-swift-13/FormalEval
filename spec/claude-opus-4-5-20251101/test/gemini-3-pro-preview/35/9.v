Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (result : R) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [1.5; 3; 2; -4; -3.5; 0; 2.5] 3.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    right; left.
    reflexivity.
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst.
    + (* x = 1.5 *)
      lra.
    + (* x = 3 *)
      lra.
    + (* x = 2 *)
      lra.
    + (* x = -4 *)
      lra.
    + (* x = -3.5 *)
      lra.
    + (* x = 0 *)
      lra.
    + (* x = 2.5 *)
      lra.
    + (* False case from empty list tail *)
      contradiction.
Qed.