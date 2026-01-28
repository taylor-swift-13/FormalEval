Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (result : R) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; -3.4; 5.6; 69.4; -9.0; 10.1] 69.4.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    right; right; right; right; right; left.
    reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.