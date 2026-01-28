Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

(* Helper for popcount on positive numbers (binary representation) *)
Fixpoint pop_pos (p : positive) : nat :=
  match p with
  | xI q => S (pop_pos q)
  | xO q => pop_pos q
  | xH => 1%nat
  end.

(* Main function using Z *)
Definition count_ones (z : Z) : nat :=
  match z with
  | Z0 => 0%nat
  | Zpos p => pop_pos p
  | Zneg p => pop_pos p
  end.

(* Comparison logic definition *)
Definition lt_custom (a b : Z) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b)%nat \/ (ones_a = ones_b /\ a < b).

(* Boolean comparison function for implementation *)
Definition lt_custom_bool (a b : Z) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if (ones_a <? ones_b)%nat then true
  else if (ones_a =? ones_b)%nat then (a <? b)
  else false.

(* Insertion sort insert function *)
Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t =>
      if lt_custom_bool x h then
        x :: l
      else
        h :: insert_sorted x t
  end.

(* Main sort implementation *)
Fixpoint sort_array_impl (input : list Z) : list Z :=
  match input with
  | [] => []
  | h :: t => insert_sorted h (sort_array_impl t)
  end.

(* Specification definition *)
Definition problem_116_spec (input output : list Z) : Prop :=
  output = sort_array_impl input.

(* Test case proof *)
Example test_problem_116 :
  problem_116_spec [15; 0; 10101010; 0; 100000; 100000] [0; 0; 15; 100000; 100000; 10101010].
Proof.
  unfold problem_116_spec.
  vm_compute.
  reflexivity.
Qed.