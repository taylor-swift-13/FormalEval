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

Definition problem_70_pre (l_in : list Z) : Prop := True.

Definition problem_70_spec (l_in l_out : list Z) : Prop :=
  StrangeSort_Min l_in l_out.

Example strange_sort_example :
  problem_70_spec [1; 2; 3; 4] [1; 4; 2; 3].
Proof.
  unfold problem_70_spec.
  apply SSMin_cons with (l_rem := [2; 3; 4]); simpl.
  - apply perm_skip. apply perm_swap.
  - split; [left; reflexivity | intros x [H | [H | [H | H]]]; subst; lia].
  - apply SSMax_cons with (l_rem := [2; 3]); simpl.
    + apply perm_swap.
    + split; [right; left; reflexivity | intros x [H | [H | H]]; subst; lia].
    + apply SSMin_cons with (l_rem := [3]); simpl.
      * apply perm_swap.
      * split; [left; reflexivity | intros x [H | H]; subst; lia].
      * apply SSMax_cons with (l_rem := []); simpl.
        -- apply Permutation_refl.
        -- split; [left; reflexivity | intros x H; inversion H].
        -- apply SSMin_nil.
Qed.