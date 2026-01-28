Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Pre: no additional constraints for `sort_third` by default *)
Definition problem_33_pre (input : list Z) : Prop := True.

(* Spec definition *)
Definition problem_33_spec (input output : list Z) : Prop :=
  (* 1. input is a Permutation of output *)
  Permutation input output /\

  (* 2. If index i is not divisible by 3, output[i] must equal input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\

  (* 3. Elements at indices divisible by 3 in output must be sorted *)
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example test_case_problem_33 : problem_33_spec 
  [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 3%Z] 
  [1%Z; 2%Z; 3%Z; 3%Z; 5%Z; 6%Z; 4%Z; 8%Z; 9%Z; 7%Z; 11%Z; 12%Z; 10%Z; 14%Z; 15%Z; 13%Z].
Proof.
  unfold problem_33_spec.
  split.
  - (* Part 1: Permutation *)
    do 3 apply perm_skip.
    transitivity (3%Z :: [4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z]).
    { symmetry. apply Permutation_cons_append. }
    apply perm_skip.
    transitivity (5%Z :: 4%Z :: [6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z]).
    { apply perm_swap. }
    apply perm_skip.
    transitivity (6%Z :: 4%Z :: [7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z]).
    { apply perm_swap. }
    apply perm_skip.
    apply perm_skip.
    transitivity (8%Z :: 7%Z :: [9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z]).
    { apply perm_swap. }
    apply perm_skip.
    transitivity (9%Z :: 7%Z :: [10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z]).
    { apply perm_swap. }
    apply perm_skip.
    apply perm_skip.
    transitivity (11%Z :: 10%Z :: [12%Z; 13%Z; 14%Z; 15%Z]).
    { apply perm_swap. }
    apply perm_skip.
    transitivity (12%Z :: 10%Z :: [13%Z; 14%Z; 15%Z]).
    { apply perm_swap. }
    apply perm_skip.
    apply perm_skip.
    transitivity (14%Z :: 13%Z :: [15%Z]).
    { apply perm_swap. }
    apply perm_skip.
    apply perm_swap.
  - split.
    + (* Part 2: Non-divisible indices equality *)
      intros i Hlen Hmod.
      do 16 (destruct i as [|i]; [ try (simpl in Hmod; lia); simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + (* Part 3: Sortedness of divisible indices *)
      intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      do 16 (destruct i as [|i]; [
        try (simpl in Hmodi; discriminate);
        do 16 (destruct j as [|j]; [
          try (simpl in Hmodj; discriminate);
          try (simpl in Hlt; lia);
          simpl; lia
        | ]);
        simpl in Hj; lia
      | ]).
      simpl in Hi; lia.
Qed.