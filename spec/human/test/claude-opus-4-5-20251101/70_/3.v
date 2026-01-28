(* def strange_sort_list(lst):
'''
Given list of integers, return list in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum and so on.

Examples:
strange_sort_list([1, 2, 3, 4]) == [1, 4, 2, 3]
strange_sort_list([5, 5, 5, 5]) == [5, 5, 5, 5]
strange_sort_list([]) == []
''' *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

Definition is_min (l : list Z) (a : Z) : Prop :=
  In a l /\ (forall x, In x l -> Z.le a x).

Definition is_max (l : list Z) (a : Z) : Prop :=
  In a l /\ (forall x, In x l -> Z.le x a).

Inductive StrangeSort_Min : list Z -> list Z -> Prop :=
  | SSMin_nil : StrangeSort_Min [] []
  | SSMin_cons : forall l l_rem x xs,
      Permutation l (x :: l_rem) ->
      is_min l x ->
      StrangeSort_Max l_rem xs ->
      StrangeSort_Min l (x :: xs)

with StrangeSort_Max : list Z -> list Z -> Prop :=
  | SSMax_nil : StrangeSort_Max [] []
  | SSMax_cons : forall l l_rem y ys,
      Permutation l (y :: l_rem) ->
      is_max l y ->
      StrangeSort_Min l_rem ys ->
      StrangeSort_Max l (y :: ys).

Definition problem_70_pre (l_in : list Z) : Prop := True.

Definition problem_70_spec (l_in l_out : list Z) : Prop :=
  StrangeSort_Min l_in l_out.

Example test_strange_sort : problem_70_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z] [1%Z; 5%Z; 2%Z; 4%Z; 3%Z].
Proof.
  unfold problem_70_spec.
  apply (SSMin_cons [1;2;3;4;5] [2;3;4;5] 1 [5;2;4;3]).
  - apply Permutation_refl.
  - unfold is_min. split.
    + simpl. left. reflexivity.
    + intros x Hx. simpl in Hx.
      destruct Hx as [H|[H|[H|[H|[H|H]]]]]; subst; try lia; try contradiction.
  - apply (SSMax_cons [2;3;4;5] [2;3;4] 5 [2;4;3]).
    + assert (Permutation [2;3;4;5] [5;2;3;4]).
      {
        apply perm_trans with [2;3;5;4].
        - apply perm_skip. apply perm_skip. apply perm_swap.
        - apply perm_trans with [2;5;3;4].
          + apply perm_skip. apply perm_swap.
          + apply perm_swap.
      }
      apply perm_trans with [5;2;3;4].
      * exact H.
      * apply Permutation_refl.
    + unfold is_max. split.
      * simpl. right. right. right. left. reflexivity.
      * intros x Hx. simpl in Hx.
        destruct Hx as [H|[H|[H|[H|H]]]]; subst; try lia; try contradiction.
    + apply (SSMin_cons [2;3;4] [3;4] 2 [4;3]).
      * apply Permutation_refl.
      * unfold is_min. split.
        -- simpl. left. reflexivity.
        -- intros x Hx. simpl in Hx.
           destruct Hx as [H|[H|[H|H]]]; subst; try lia; try contradiction.
      * apply (SSMax_cons [3;4] [3] 4 [3]).
        -- assert (Permutation [3;4] [4;3]).
           { apply perm_swap. }
           apply perm_trans with [4;3].
           ++ exact H.
           ++ apply Permutation_refl.
        -- unfold is_max. split.
           ++ simpl. right. left. reflexivity.
           ++ intros x Hx. simpl in Hx.
              destruct Hx as [H|[H|H]]; subst; try lia; try contradiction.
        -- apply (SSMin_cons [3] [] 3 []).
           ++ apply Permutation_refl.
           ++ unfold is_min. split.
              ** simpl. left. reflexivity.
              ** intros x Hx. simpl in Hx.
                 destruct Hx as [H|H]; subst; try lia; try contradiction.
           ++ apply SSMax_nil.
Qed.