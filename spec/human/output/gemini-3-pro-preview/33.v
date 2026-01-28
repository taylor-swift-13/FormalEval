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

Example test_case_problem_33 : problem_33_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold problem_33_spec.
  split.
  - (* Part 1: Permutation *)
    apply Permutation_refl.
  - split.
    + (* Part 2: Non-divisible indices equality *)
      intros i Hlen Hmod.
      simpl in Hlen.
      (* Exhaustive case analysis on index i *)
      destruct i as [| [| [| i'] ] ].
      * (* i = 0 *)
        simpl in Hmod.
        (* 0 mod 3 = 0, contradiction with Hmod (i mod 3 <> 0) *)
        lia.
      * (* i = 1 *)
        simpl. reflexivity.
      * (* i = 2 *)
        simpl. reflexivity.
      * (* i >= 3 *)
        (* Contradiction with length constraint Hlen *)
        lia.
    + (* Part 3: Sortedness of divisible indices *)
      intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      simpl in Hi, Hj.
      (* Exhaustive case analysis on i to show it must be 0 *)
      destruct i as [| [| [| i'] ] ].
      * (* i = 0 *)
        (* Now analyze j *)
        destruct j as [| [| [| j'] ] ].
        -- (* j = 0 *)
           (* i < j becomes 0 < 0, contradiction *)
           lia.
        -- (* j = 1 *)
           simpl in Hmodj.
           (* 1 mod 3 = 1 <> 0, contradiction *)
           discriminate.
        -- (* j = 2 *)
           simpl in Hmodj.
           (* 2 mod 3 = 2 <> 0, contradiction *)
           discriminate.
        -- (* j >= 3 *)
           lia.
      * (* i = 1 *)
        simpl in Hmodi. discriminate.
      * (* i = 2 *)
        simpl in Hmodi. discriminate.
      * (* i >= 3 *)
        lia.
Qed.