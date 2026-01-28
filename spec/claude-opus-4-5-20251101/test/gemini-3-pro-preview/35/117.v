Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (result : R) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; 5.6; 99.9; -8.601314347821834; 10.1] 99.9.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    right; right; right; right; left.
    reflexivity.
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst.
    + (* x = 1.2 *)
      lra.
    + (* x = -4.5 *)
      lra.
    + (* x = -3.4 *)
      lra.
    + (* x = 5.6 *)
      lra.
    + (* x = 99.9 *)
      lra.
    + (* x = -8.601314347821834 *)
      lra.
    + (* x = 10.1 *)
      lra.
    + (* False case from empty list tail *)
      contradiction.
Qed.