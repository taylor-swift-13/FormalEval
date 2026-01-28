Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

(* Helper function with fuel to ensure termination for structural recursion *)
Fixpoint count_ones_helper (n fuel : nat) : nat :=
  match fuel with
  | 0%nat => 0%nat 
  | S fuel' => 
      match n with
      | 0%nat => 0%nat 
      | _ => ((n mod 2) + count_ones_helper (n / 2) fuel')%nat
      end
  end.

(* Main function using n itself as fuel *)
Definition count_ones (z : Z) : nat :=
  let n := Z.to_nat (Z.abs z) in
  count_ones_helper n n.

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
  problem_116_spec [-2; -3; -4; -5; -6] [-4; -2; -6; -5; -3].
Proof.
  unfold problem_116_spec.
  reflexivity.
Qed.