Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

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

Definition problem_70_spec (l_in l_out : list Z) : Prop :=
  StrangeSort_Min l_in l_out.

Lemma is_min_1234_1 : is_min [1; 2; 3; 4] 1.
Proof.
  unfold is_min.
  split.
  - simpl; auto.
  - intros x H.
    simpl in H; destruct H as [H|H]; [subst x; apply Z.le_refl|].
    destruct H as [H|H]; [subst x; apply Zle_plus_1_compat; apply Z.le_refl|].
    destruct H as [H|H]; [subst x; apply Zle_plus_1_compat; apply Zle_plus_1_compat; apply Z.le_refl|].
    destruct H; apply Zle_plus_1_compat; apply Zle_plus_1_compat; apply Zle_plus_1_compat; apply Z.le_refl.
Qed.

Lemma is_max_234_4 : is_max [2; 3; 4] 4.
Proof.
  unfold is_max.
  split.
  - simpl; right; right; left; reflexivity.
  - intros x H.
    simpl in H; destruct H as [H|H]; [subst x; apply Zle_minus_1_compat; apply Zle_minus_1_compat; apply Z.le_refl|].
    destruct H as [H|H]; [subst x; apply Zle_minus_1_compat; apply Z.le_refl|].
    destruct H as [H|H]; [subst x; apply Z.le_refl|].
    destruct H.
Qed.

Lemma is_min_23_2 : is_min [2; 3] 2.
Proof.
  unfold is_min.
  split.
  - simpl; auto.
  - intros x H.
    simpl in H; destruct H as [H|H]; [subst x; apply Z.le_refl|].
    destruct H as [H|H]; [subst x; apply Zle_plus_1_compat; apply Z.le_refl|].
    destruct H.
Qed.

Lemma is_max_3_3 : is_max [3] 3.
Proof.
  unfold is_max.
  split.
  - simpl; auto.
  - intros x H.
    simpl in H; destruct H as [H|H]; [subst x; apply Z.le_refl|].
    destruct H.
Qed.

Example test_strange_sort : problem_70_spec [1; 2; 3; 4] [1; 4; 2; 3].
Proof.
  unfold problem_70_spec.
  apply SSMin_cons with (l_rem := [2; 3; 4]) (x := 1).
  - apply Permutation_refl.
  - apply is_min_1234_1.
  - apply SSMax_cons with (l_rem := [2; 3]) (y := 4).
    + apply Permutation_refl.
    + apply is_max_234_4.
    + apply SSMin_cons with (l_rem := [3]) (x := 2).
      * apply Permutation_refl.
      * apply is_min_23_2.
      * apply SSMax_cons with (l_rem := []) (y := 3).
        { apply Permutation_refl. }
        { apply is_max_3_3. }
        { apply SSMin_nil. }
Qed.