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

Example test_strange_sort : problem_70_spec [4%Z; 10%Z; 9%Z; 75%Z; 5%Z; 5%Z] [4%Z; 75%Z; 5%Z; 10%Z; 5%Z; 9%Z].
Proof.
  unfold problem_70_spec.
  apply (SSMin_cons [4;10;9;75;5;5] [10;9;75;5;5] 4 [75;5;10;5;9]).
  - apply Permutation_refl.
  - unfold is_min. split.
    + simpl. left. reflexivity.
    + intros x Hx. simpl in Hx.
      destruct Hx as [H|[H|[H|[H|[H|[H|H]]]]]]; subst; try lia; try contradiction.
  - apply (SSMax_cons [10;9;75;5;5] [10;9;5;5] 75 [5;10;5;9]).
    + assert (Permutation [10;9;75;5;5] [75;10;9;5;5]).
      {
        apply perm_trans with [10;75;9;5;5].
        - apply perm_skip. apply perm_swap.
        - apply perm_swap.
      }
      apply perm_trans with [75;10;9;5;5].
      * exact H.
      * apply Permutation_refl.
    + unfold is_max. split.
      * simpl. right. right. left. reflexivity.
      * intros x Hx. simpl in Hx.
        destruct Hx as [H|[H|[H|[H|[H|H]]]]]; subst; try lia; try contradiction.
    + apply (SSMin_cons [10;9;5;5] [10;9;5] 5 [10;5;9]).
      * assert (Permutation [10;9;5;5] [5;10;9;5]).
        {
          apply perm_trans with [10;9;5;5].
          - apply Permutation_refl.
          - apply perm_trans with [5;9;10;5].
            + apply perm_trans with [9;10;5;5].
              * apply perm_swap.
              * apply perm_trans with [9;5;10;5].
                -- apply perm_skip. apply perm_swap.
                -- apply perm_swap.
            + apply perm_skip. apply perm_swap.
        }
        apply perm_trans with [5;10;9;5].
        -- exact H.
        -- apply Permutation_refl.
      * unfold is_min. split.
        -- simpl. right. right. left. reflexivity.
        -- intros x Hx. simpl in Hx.
           destruct Hx as [H|[H|[H|[H|H]]]]; subst; try lia; try contradiction.
      * apply (SSMax_cons [10;9;5] [9;5] 10 [5;9]).
        -- apply Permutation_refl.
        -- unfold is_max. split.
           ++ simpl. left. reflexivity.
           ++ intros x Hx. simpl in Hx.
              destruct Hx as [H|[H|[H|H]]]; subst; try lia; try contradiction.
        -- apply (SSMin_cons [9;5] [9] 5 [9]).
           ++ assert (Permutation [9;5] [5;9]).
              { apply perm_swap. }
              exact H.
           ++ unfold is_min. split.
              ** simpl. right. left. reflexivity.
              ** intros x Hx. simpl in Hx.
                 destruct Hx as [H|[H|H]]; subst; try lia; try contradiction.
           ++ apply (SSMax_cons [9] [] 9 []).
              ** apply Permutation_refl.
              ** unfold is_max. split.
                 --- simpl. left. reflexivity.
                 --- intros x Hx. simpl in Hx.
                     destruct Hx as [H|H]; subst; try lia; try contradiction.
              ** apply SSMin_nil.
Qed.