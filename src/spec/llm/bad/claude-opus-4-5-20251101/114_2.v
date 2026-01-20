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

Lemma sum_list_app : forall l1 l2, sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  intros l1 l2.
  induction l1 as [|h t IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma all_elements_test2 : forall x, In x [-1; -2; -3] -> x = -1 \/ x = -2 \/ x = -3.
Proof.
  intros x Hx.
  simpl in Hx.
  destruct Hx as [H|[H|[H|H]]]; try lia; try contradiction.
  - left. lia.
  - right. left. lia.
  - right. right. lia.
Qed.

Lemma subarray_of_test2 : forall sub,
  non_empty sub ->
  is_subarray sub [-1; -2; -3] ->
  sub = [-1] \/ sub = [-2] \/ sub = [-3] \/
  sub = [-1; -2] \/ sub = [-2; -3] \/
  sub = [-1; -2; -3].
Proof.
  intros sub Hne [prefix [suffix Heq]].
  destruct prefix as [|p1 prefix'].
  - simpl in Heq.
    destruct sub as [|s1 sub'].
    + exfalso. apply Hne. reflexivity.
    + injection Heq as Hs1 Hrest.
      destruct sub' as [|s2 sub''].
      * left. reflexivity.
      * injection Hrest as Hs2 Hrest'.
        destruct sub'' as [|s3 sub'''].
        -- right. right. right. left. reflexivity.
        -- injection Hrest' as Hs3 Hrest''.
           destruct sub''' as [|s4 sub''''].
           ++ right. right. right. right. right. reflexivity.
           ++ destruct suffix; discriminate Hrest''.
  - destruct prefix' as [|p2 prefix''].
    + simpl in Heq. injection Heq as Hp1 Hrest.
      destruct sub as [|s1 sub'].
      * exfalso. apply Hne. reflexivity.
      * injection Hrest as Hs1 Hrest'.
        destruct sub' as [|s2 sub''].
        -- right. left. reflexivity.
        -- injection Hrest' as Hs2 Hrest''.
           destruct sub'' as [|s3 sub'''].
           ++ right. right. right. right. left. reflexivity.
           ++ destruct suffix; discriminate Hrest''.
    + destruct prefix'' as [|p3 prefix'''].
      * simpl in Heq. injection Heq as Hp1 Hrest.
        injection Hrest as Hp2 Hrest'.
        destruct sub as [|s1 sub'].
        -- exfalso. apply Hne. reflexivity.
        -- injection Hrest' as Hs1 Hrest''.
           destruct sub' as [|s2 sub''].
           ++ right. right. left. reflexivity.
           ++ destruct suffix; discriminate Hrest''.
      * simpl in Heq. injection Heq as Hp1 Hrest.
        injection Hrest as Hp2 Hrest'.
        injection Hrest' as Hp3 Hrest''.
        destruct sub as [|s1 sub'].
        -- exfalso. apply Hne. reflexivity.
        -- destruct suffix; discriminate Hrest''.
Qed.

Example test_minSubArraySum : minSubArraySum_spec [-1; -2; -3] (-6).
Proof.
  unfold minSubArraySum_spec.
  split.
  - discriminate.
  - split.
    + exists [-1; -2; -3].
      split.
      * unfold non_empty. discriminate.
      * split.
        -- unfold is_subarray.
           exists [], [].
           reflexivity.
        -- reflexivity.
    + intros sub Hne Hsub.
      destruct (subarray_of_test2 sub Hne Hsub) as [H|[H|[H|[H|[H|H]]]]];
      rewrite H; simpl; lia.
Qed.