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
  [11%Z; 22%Z; 33%Z; 44%Z; 55%Z; 66%Z; 77%Z; 88%Z; 88%Z; 32%Z; 99%Z; 77%Z; 77%Z; 11%Z] 
  [11%Z; 22%Z; 33%Z; 32%Z; 55%Z; 66%Z; 44%Z; 88%Z; 88%Z; 77%Z; 99%Z; 77%Z; 77%Z; 11%Z].
Proof.
  unfold problem_33_spec.
  split.
  - apply Permutation_cons; [reflexivity|].
    apply Permutation_cons; [reflexivity|].
    apply Permutation_cons; [reflexivity|].
    apply Permutation_trans with (32%Z :: [44%Z; 55%Z; 66%Z; 77%Z; 88%Z; 88%Z] ++ [99%Z; 77%Z; 77%Z; 11%Z]).
    { apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons; [reflexivity|].
    simpl.
    apply Permutation_trans with (55%Z :: [44%Z] ++ [66%Z; 77%Z; 88%Z; 88%Z; 99%Z; 77%Z; 77%Z; 11%Z]).
    { apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons; [reflexivity|].
    simpl.
    apply Permutation_trans with (66%Z :: [44%Z] ++ [77%Z; 88%Z; 88%Z; 99%Z; 77%Z; 77%Z; 11%Z]).
    { apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons; [reflexivity|].
    simpl.
    apply Permutation_cons; [reflexivity|].
    apply Permutation_trans with (88%Z :: [77%Z] ++ [88%Z; 99%Z; 77%Z; 77%Z; 11%Z]).
    { apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons; [reflexivity|].
    simpl.
    apply Permutation_trans with (88%Z :: [77%Z] ++ [99%Z; 77%Z; 77%Z; 11%Z]).
    { apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons; [reflexivity|].
    simpl.
    apply Permutation_refl.
  - split.
    + intros i Hlen Hmod.
      do 14 (destruct i as [|i]; [
        try (simpl in Hmod; exfalso; apply Hmod; reflexivity);
        try (simpl; reflexivity)
      | ]).
      simpl in Hlen; lia.
    + intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      do 14 (destruct i as [|i]; [
        do 14 (destruct j as [|j]; [
          try (simpl in Hmodi; discriminate);
          try (simpl in Hmodj; discriminate);
          try (simpl in Hlt; lia);
          try (simpl; lia)
        | ]);
        simpl in Hj; lia
      | ]).
      simpl in Hi; lia.
Qed.