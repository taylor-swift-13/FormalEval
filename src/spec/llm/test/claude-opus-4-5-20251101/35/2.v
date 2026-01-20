Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [5%Z; 3%Z; -5%Z; 2%Z; -3%Z; 3%Z; 9%Z; 0%Z; 124%Z; 1%Z; -10%Z] 124%Z.
Proof.
  unfold max_element_spec.
  split.
  - discriminate.
  - split.
    + simpl. right. right. right. right. right. right. right. right. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]].
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * contradiction.
Qed.