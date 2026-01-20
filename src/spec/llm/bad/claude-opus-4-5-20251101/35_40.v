Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition max_element_spec (l : list R) (result : R) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> (x <= result)%R.

Example test_max_element : max_element_spec [1.5%R; 3%R; 2%R; (-4)%R; (-3.5)%R; 0%R] 3%R.
Proof.
  unfold max_element_spec.
  split.
  - discriminate.
  - split.
    + simpl. right. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [H | [H | [H | [H | [H | [H | H]]]]]].
      * subst x. lra.
      * subst x. lra.
      * subst x. lra.
      * subst x. lra.
      * subst x. lra.
      * subst x. lra.
      * contradiction.
Qed.