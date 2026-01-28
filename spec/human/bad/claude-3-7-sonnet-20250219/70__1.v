Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.

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

(* Lemmas for minimal elements *)

Lemma min_1_2_3_4_is_1 : is_min [1;2;3;4] 1.
Proof.
  split.
  - simpl; left; reflexivity.
  - intros x Hx.
    destruct Hx as [->|[->|[->|[]]]]; lia.
Qed.

Lemma max_2_3_4_is_4 : is_max [2;3;4] 4.
Proof.
  split.
  - simpl. repeat right; left; reflexivity.
  - intros x Hx.
    destruct Hx as [->|[->|[->|[]]]]; lia.
Qed.

Lemma min_2_3_is_2 : is_min [2;3] 2.
Proof.
  split.
  - simpl; left; reflexivity.
  - intros x Hx.
    destruct Hx as [->|[->|[]]]; lia.
Qed.

Lemma max_3_is_3 : is_max [3] 3.
Proof.
  split.
  - simpl; left; reflexivity.
  - intros x Hx.
    destruct Hx; subst; lia.
Qed.

Example test_strange_sort_1_2_3_4 :
  problem_70_spec [1;2;3;4] [1;4;2;3].
Proof.
  unfold problem_70_spec.
  apply SSMin_cons with (l_rem := [2;3;4]).
  - (* Permutation *)
    simpl. apply Permutation_refl.
  - apply min_1_2_3_4_is_1.
  - apply SSMax_cons with (l_rem := [2;3]).
    + simpl. apply Permutation_refl.
    + apply max_2_3_4_is_4.
    + apply SSMin_cons with (l_rem := [3]).
      * simpl. apply Permutation_refl.
      * apply min_2_3_is_2.
      * apply SSMax_cons with (l_rem := []).
        -- simpl. apply Permutation_refl.
        -- apply max_3_is_3.
        -- apply SSMin_nil.
Qed.