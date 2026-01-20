Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_subarray {A : Type} (sub arr : list A) : Prop :=
  exists prefix suffix, arr = prefix ++ sub ++ suffix.

Definition non_empty {A : Type} (l : list A) : Prop :=
  l <> [].

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition minSubArraySum_spec (nums : list Z) (result : Z) : Prop :=
  nums <> [] /\
  (exists sub : list Z, 
    non_empty sub /\ 
    is_subarray sub nums /\ 
    sum_list sub = result) /\
  (forall sub : list Z, 
    non_empty sub -> 
    is_subarray sub nums -> 
    result <= sum_list sub).

Lemma sum_list_nonneg : forall l : list Z,
  (forall x, In x l -> 1 <= x) -> 0 <= sum_list l.
Proof.
  intros l H.
  induction l as [|h t IH].
  - simpl. lia.
  - simpl.
    assert (1 <= h) by (apply H; left; reflexivity).
    assert (0 <= sum_list t).
    {
      apply IH. intros x Hx. apply H. right. exact Hx.
    }
    lia.
Qed.

Lemma all_elements_ge_7 : forall x, In x [7] -> 7 <= x.
Proof.
  intros x Hx.
  simpl in Hx.
  destruct Hx as [H|H]; try lia; try contradiction.
Qed.

Lemma subarray_elements : forall (sub : list Z) (arr : list Z),
  is_subarray sub arr ->
  forall x, In x sub -> In x arr.
Proof.
  intros sub arr [prefix [suffix Heq]] x Hx.
  rewrite Heq.
  apply in_or_app. right.
  apply in_or_app. left.
  exact Hx.
Qed.

Lemma sum_list_pos_lower_bound_7 : forall (l : list Z),
  non_empty l ->
  (forall x, In x l -> 7 <= x) ->
  7 <= sum_list l.
Proof.
  intros l Hne Hall.
  destruct l as [|h t].
  - unfold non_empty in Hne. exfalso. apply Hne. reflexivity.
  - simpl.
    assert (7 <= h) by (apply Hall; left; reflexivity).
    assert (0 <= sum_list t).
    {
      apply sum_list_nonneg. intros x Hx. 
      assert (7 <= x) by (apply Hall; right; exact Hx).
      lia.
    }
    lia.
Qed.

Lemma singleton_not_nil : [7] <> [].
Proof.
  intro H. discriminate H.
Qed.

Example test_minSubArraySum : minSubArraySum_spec [7] 7.
Proof.
  unfold minSubArraySum_spec.
  split.
  - exact singleton_not_nil.
  - split.
    + exists [7].
      split.
      * unfold non_empty. intro H. discriminate H.
      * split.
        -- unfold is_subarray.
           exists [], [].
           reflexivity.
        -- reflexivity.
    + intros sub Hne Hsub.
      assert (Helem: forall x, In x sub -> In x [7]).
      {
        intros x Hx. eapply subarray_elements; eauto.
      }
      assert (Hge7: forall x, In x sub -> 7 <= x).
      {
        intros x Hx. apply all_elements_ge_7. apply Helem. exact Hx.
      }
      apply sum_list_pos_lower_bound_7; assumption.
Qed.