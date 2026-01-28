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
  [5%Z; 10%Z; 15%Z; 20%Z; 25%Z; 30%Z; 35%Z; 40%Z; 45%Z; 50%Z; 55%Z; 60%Z] 
  [5%Z; 10%Z; 15%Z; 20%Z; 25%Z; 30%Z; 35%Z; 40%Z; 45%Z; 50%Z; 55%Z; 60%Z].
Proof.
  unfold problem_33_spec.
  split.
  - (* Part 1: Permutation *)
    apply Permutation_refl.
  - split.
    + (* Part 2: Non-divisible indices equality *)
      intros i Hlen Hmod.
      (* Since input = output, this is trivial *)
      reflexivity.
    + (* Part 3: Sortedness of divisible indices *)
      intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      simpl in Hi, Hj.
      (* Exhaustive case analysis on i *)
      repeat (destruct i; [| try lia]).
      (* Filter invalid i based on Hmodi *)
      all: simpl in Hmodi; try discriminate.
      (* Exhaustive case analysis on j *)
      all: repeat (destruct j; [| try lia]).
      (* Filter invalid j based on Hmodj *)
      all: simpl in Hmodj; try discriminate.
      (* Filter invalid pairs based on i < j *)
      all: simpl in Hlt; try lia.
      (* Verify values for valid pairs *)
      all: simpl; lia.
Qed.