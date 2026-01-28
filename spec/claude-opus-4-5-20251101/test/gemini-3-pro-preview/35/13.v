Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [50; 49; 100; 48; 47; 46] 100.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    right; right; left.
    reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]]; subst; try lia; try contradiction.
Qed.