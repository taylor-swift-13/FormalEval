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

Example test_case_problem_33 : problem_33_spec [9%Z; 12%Z; 15%Z; 6%Z; 3%Z; 8%Z; 10%Z; 23%Z; 7%Z; 23%Z] [6%Z; 12%Z; 15%Z; 9%Z; 3%Z; 8%Z; 10%Z; 23%Z; 7%Z; 23%Z].
Proof.
  unfold problem_33_spec.
  split.
  - apply perm_trans with (l' := 6%Z :: 9%Z :: 12%Z :: 15%Z :: [3%Z; 8%Z; 10%Z; 23%Z; 7%Z; 23%Z]).
    + apply perm_trans with (l' := 9%Z :: 12%Z :: 6%Z :: 15%Z :: [3%Z; 8%Z; 10%Z; 23%Z; 7%Z; 23%Z]).
      * apply perm_skip. apply perm_skip. apply perm_swap.
      * apply perm_trans with (l' := 9%Z :: 6%Z :: 12%Z :: 15%Z :: [3%Z; 8%Z; 10%Z; 23%Z; 7%Z; 23%Z]).
        { apply perm_skip. apply perm_swap. }
        { apply perm_swap. }
    + apply perm_skip.
      apply perm_trans with (l' := 12%Z :: 9%Z :: 15%Z :: [3%Z; 8%Z; 10%Z; 23%Z; 7%Z; 23%Z]).
      * apply perm_swap.
      * apply perm_trans with (l' := 12%Z :: 15%Z :: 9%Z :: [3%Z; 8%Z; 10%Z; 23%Z; 7%Z; 23%Z]).
        { apply perm_skip. apply perm_swap. }
        { apply Permutation_refl. }
  - split.
    + intros i Hlen Hmod.
      do 10 (destruct i as [|i]; [
        simpl in Hmod; try lia; simpl; reflexivity
      | ]).
      simpl in Hlen; lia.
    + intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      do 10 (destruct i as [|i]; [
        do 10 (destruct j as [|j]; [
           simpl in Hmodi, Hmodj, Hlt;
           try discriminate;
           try lia;
           simpl; try lia
        | ]);
        simpl in Hj; lia
      | ]).
      simpl in Hi; lia.
Qed.