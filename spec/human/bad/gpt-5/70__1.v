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

Example problem_70_test :
  problem_70_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 4%Z; 2%Z; 3%Z].
Proof.
  unfold problem_70_spec.
  eapply SSMin_cons with (x := 1%Z) (l_rem := [2%Z; 3%Z; 4%Z]) (xs := [4%Z; 2%Z; 3%Z]).
  - apply Permutation_refl.
  - split.
    + simpl. left. reflexivity.
    + intros x Hx. simpl in Hx.
      destruct Hx as [Hx | Hx]; [subst; lia|].
      simpl in Hx. destruct Hx as [Hx | Hx]; [subst; lia|].
      simpl in Hx. destruct Hx as [Hx | Hx]; [subst; lia|].
      simpl in Hx. contradiction.
  - eapply SSMax_cons with (y := 4%Z) (l_rem := [2%Z; 3%Z]) (ys := [2%Z; 3%Z]).
    + change [2%Z; 3%Z; 4%Z] with ([2%Z; 3%Z] ++ [4%Z]).
      change (4%Z :: [2%Z; 3%Z]) with (4%Z :: [2%Z; 3%Z] ++ []).
      apply Permutation_middle.
    + split.
      * simpl. right. right. left. reflexivity.
      * intros x Hx. simpl in Hx.
        destruct Hx as [Hx | Hx]; [subst; lia|].
        simpl in Hx. destruct Hx as [Hx | Hx]; [subst; lia|].
        simpl in Hx. destruct Hx as [Hx | Hx]; [subst; lia|].
        simpl in Hx. contradiction.
    + eapply SSMin_cons with (x := 2%Z) (l_rem := [3%Z]) (xs := [3%Z]).
      * apply Permutation_refl.
      * split.
        { simpl. left. reflexivity. }
        { intros x Hx. simpl in Hx.
          destruct Hx as [Hx | Hx]; [subst; lia|].
          simpl in Hx. destruct Hx as [Hx | Hx]; [subst; lia|].
          simpl in Hx. contradiction. }
      * eapply SSMax_cons with (y := 3%Z) (l_rem := []) (ys := []).
        { apply Permutation_refl. }
        { split.
          - simpl. left. reflexivity.
          - intros x Hx. simpl in Hx.
            destruct Hx as [Hx | Hx]; [subst; lia|].
            contradiction. }
        { apply SSMin_nil. }
Qed.