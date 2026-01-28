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

Example test_case_problem_33 : problem_33_spec [2%Z; 35%Z; 1%Z; 3%Z; 7%Z; 8%Z; 9%Z; 10%Z] [2%Z; 35%Z; 1%Z; 3%Z; 7%Z; 8%Z; 9%Z; 10%Z].
Proof.
  unfold problem_33_spec.
  split.
  - apply Permutation_refl.
  - split.
    + intros i Hlen Hmod. reflexivity.
    + intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      simpl in Hi, Hj.
      destruct i as [| [| [| [| [| [| [| [| ]]]]]]]].
      * destruct j as [| [| [| [| [| [| [| [| ]]]]]]]];
        try (simpl in Hmodj; discriminate); try lia; simpl; lia.
      * simpl in Hmodi; discriminate.
      * simpl in Hmodi; discriminate.
      * destruct j as [| [| [| [| [| [| [| [| ]]]]]]]];
        try (simpl in Hmodj; discriminate); try lia; simpl; lia.
      * simpl in Hmodi; discriminate.
      * simpl in Hmodi; discriminate.
      * destruct j as [| [| [| [| [| [| [| [| ]]]]]]]];
        try (simpl in Hmodj; discriminate); try lia; simpl; lia.
      * simpl in Hmodi; discriminate.
      * lia.
Qed.