Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

(* Pre-condition for sort_third, which is trivial here *)
Definition problem_33_pre (input : list Z) : Prop := True.

(* Specification for sort_third *)
Definition problem_33_spec (input output : list Z) : Prop :=
  (* 1. input and output have the same length *)
  length input = length output /\

  (* 2. For indices not divisible by 3, output[i] must equal input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\

  (* 3. For each index divisible by 3 in output, there exists an index in input with the same value *)
  (forall (i : nat), (i < length output)%nat -> (i mod 3 = 0) ->
    exists j, (j < length input)%nat /\ (j mod 3 = 0) /\ nth i output 0%Z = nth j input 0%Z) /\

  (* 4. For each index divisible by 3 in input, there exists an index in output with the same value *)
  (forall (i : nat), (i < length input)%nat -> (i mod 3 = 0) ->
    exists j, (j < length output)%nat /\ (j mod 3 = 0) /\ nth j output 0%Z = nth i input 0%Z) /\

  (* 5. Indices divisible by 3 in output must be sorted in non-decreasing order *)
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example test_sort_third : problem_33_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold problem_33_spec.
  split.
  - reflexivity.
  - split.
    + intros i Hi Hmod.
      destruct i; simpl in *; try lia.
      destruct i; simpl in *; try lia.
      destruct i; simpl in *; try lia.
      lia.
    + split.
      * intros i Hi Hmod.
        destruct i; simpl in *; try lia.
        exists 0%nat. repeat split; try lia.
      * split.
        -- intros i Hi Hmod.
           destruct i; simpl in *; try lia.
           exists 0%nat. repeat split; try lia.
        -- intros i j [Hi [Hj [Hmod_i [Hmod_j Hij]]]].
           destruct i; simpl in *; try lia.
           destruct i; simpl in *; try lia.
           destruct i; simpl in *; try lia.
Qed.