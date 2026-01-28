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

Example test_strange_sort : problem_70_spec [5%Z; 6%Z; 7%Z; 8%Z; 9%Z] [5%Z; 9%Z; 6%Z; 8%Z; 7%Z].
Proof.
  unfold problem_70_spec.
  apply (SSMin_cons [5;6;7;8;9] [6;7;8;9] 5 [9;6;8;7]).
  - apply Permutation_refl.
  - unfold is_min. split.
    + simpl. left. reflexivity.
    + intros x Hx. simpl in Hx.
      destruct Hx as [H|[H|[H|[H|[H|H]]]]]; subst; try lia; try contradiction.
  - apply (SSMax_cons [6;7;8;9] [6;7;8] 9 [6;8;7]).
    + assert (Permutation [6;7;8;9] [9;6;7;8]).
      {
        apply perm_trans with [6;7;9;8].
        - apply perm_skip. apply perm_skip. apply perm_swap.
        - apply perm_trans with [6;9;7;8].
          + apply perm_skip. apply perm_swap.
          + apply perm_swap.
      }
      apply perm_trans with [9;6;7;8].
      * exact H.
      * apply Permutation_refl.
    + unfold is_max. split.
      * simpl. right. right. right. left. reflexivity.
      * intros x Hx. simpl in Hx.
        destruct Hx as [H|[H|[H|[H|H]]]]; subst; try lia; try contradiction.
    + apply (SSMin_cons [6;7;8] [7;8] 6 [8;7]).
      * apply Permutation_refl.
      * unfold is_min. split.
        -- simpl. left. reflexivity.
        -- intros x Hx. simpl in Hx.
           destruct Hx as [H|[H|[H|H]]]; subst; try lia; try contradiction.
      * apply (SSMax_cons [7;8] [7] 8 [7]).
        -- assert (Permutation [7;8] [8;7]).
           { apply perm_swap. }
           apply perm_trans with [8;7].
           ++ exact H.
           ++ apply Permutation_refl.
        -- unfold is_max. split.
           ++ simpl. right. left. reflexivity.
           ++ intros x Hx. simpl in Hx.
              destruct Hx as [H|[H|H]]; subst; try lia; try contradiction.
        -- apply (SSMin_cons [7] [] 7 []).
           ++ apply Permutation_refl.
           ++ unfold is_min. split.
              ** simpl. left. reflexivity.
              ** intros x Hx. simpl in Hx.
                 destruct Hx as [H|H]; subst; try lia; try contradiction.
           ++ apply SSMax_nil.
Qed.