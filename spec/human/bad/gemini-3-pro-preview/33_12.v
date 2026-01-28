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

Example test_case_problem_33 : problem_33_spec [2%Z; 10%Z; 20%Z; 15%Z; 18%Z; 13%Z; 7%Z] [2%Z; 10%Z; 20%Z; 7%Z; 18%Z; 13%Z; 15%Z].
Proof.
  unfold problem_33_spec.
  split.
  - (* Part 1: Permutation *)
    apply Permutation_cons. apply Permutation_cons. apply Permutation_cons.
    eapply Permutation_trans.
    + apply Permutation_app_comm with (l := [15%Z]) (l' := [18%Z; 13%Z; 7%Z]).
    + simpl. apply Permutation_app_tail.
      apply Permutation_app_comm with (l := [18%Z; 13%Z]) (l' := [7%Z]).
  - split.
    + (* Part 2: Non-divisible indices equality *)
      intros i Hlen Hmod.
      do 7 (destruct i as [|i]; [
        try (simpl in Hmod; lia);
        simpl; reflexivity
      | ]).
      simpl in Hlen; lia.
    + (* Part 3: Sortedness of divisible indices *)
      intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      do 7 (destruct i as [|i]; [
        try (simpl in Hmodi; discriminate);
        do 7 (destruct j as [|j]; [
             try (simpl in Hmodj; discriminate);
             try (simpl in Hlt; lia);
             simpl; lia
           | ]);
           simpl in Hj; try lia
      | ]).
      simpl in Hi; lia.
Qed.