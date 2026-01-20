Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [2%Z; 48%Z; 9%Z; 8%Z; 6%Z; 7%Z; 9%Z] 48%Z.
Proof.
  unfold max_element_spec.
  split.
  - discriminate.
  - split.
    + simpl. right. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * contradiction.
Qed.