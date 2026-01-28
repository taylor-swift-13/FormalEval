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

Example test_case_problem_33 : problem_33_spec [5%Z; 6%Z; 3%Z; 4%Z; 8%Z; 9%Z; 2%Z] [2%Z; 6%Z; 3%Z; 4%Z; 8%Z; 9%Z; 5%Z].
Proof.
  unfold problem_33_spec.
  split.
  - (* Part 1: Permutation *)
    (* We show [5; 6; 3; 4; 8; 9; 2] is a permutation of [2; 6; 3; 4; 8; 9; 5] *)
    (* Move 2 to the front of the first list *)
    replace [5%Z; 6%Z; 3%Z; 4%Z; 8%Z; 9%Z; 2%Z] with ([5%Z; 6%Z; 3%Z; 4%Z; 8%Z; 9%Z] ++ [2%Z]) by reflexivity.
    apply Permutation_trans with (l' := [2%Z] ++ [5%Z; 6%Z; 3%Z; 4%Z; 8%Z; 9%Z]).
    apply Permutation_app_comm.
    simpl. apply perm_skip.
    (* Now show [5; 6; 3; 4; 8; 9] is a permutation of [6; 3; 4; 8; 9; 5] *)
    (* Move 5 to the end of the second list (or rather, match 5 at end) *)
    replace [5%Z; 6%Z; 3%Z; 4%Z; 8%Z; 9%Z] with ([5%Z] ++ [6%Z; 3%Z; 4%Z; 8%Z; 9%Z]) by reflexivity.
    apply Permutation_trans with (l' := [6%Z; 3%Z; 4%Z; 8%Z; 9%Z] ++ [5%Z]).
    apply Permutation_app_comm.
    simpl. apply Permutation_refl.
  - split.
    + (* Part 2: Non-divisible indices equality *)
      intros i Hlen Hmod.
      (* Exhaustive case analysis on index i up to length 7 *)
      do 7 (destruct i; [
        (* For specific i, check if mod 3 <> 0 *)
        try (simpl in Hmod; lia); (* If i mod 3 = 0, contradiction *)
        simpl; reflexivity         (* If i mod 3 <> 0, check equality *)
      | ]).
      (* For i >= 7 *)
      simpl in Hlen; lia.
    + (* Part 3: Sortedness of divisible indices *)
      intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      (* Exhaustive case analysis on i *)
      do 7 (destruct i; [
        (* Check i mod 3 = 0 *)
        try (simpl in Hmodi; discriminate);
        (* Exhaustive case analysis on j *)
        do 7 (destruct j; [
           (* Check j mod 3 = 0 *)
           try (simpl in Hmodj; discriminate);
           (* Check i < j *)
           try (simpl in Hlt; lia);
           (* Check sortedness *)
           simpl; lia
        | ]);
        (* j >= 7 *)
        simpl in Hj; lia
      | ]).
      (* i >= 7 *)
      simpl in Hi; lia.
Qed.