Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [2; 2; 2; 2; 2] 2.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    left.
    reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]]; subst.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + contradiction.
Qed.