Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope N_scope.

(* Helper function to count ones in a positive number *)
Fixpoint count_ones_pos (p : positive) : N :=
  match p with
  | xH => 1
  | xO p' => count_ones_pos p'
  | xI p' => 1 + count_ones_pos p'
  end.

(* Main function to count ones in N *)
Definition count_ones (n : N) : N :=
  match n with
  | N0 => 0
  | Npos p => count_ones_pos p
  end.

(* Comparison logic definition *)
Definition lt_custom (a b : N) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

(* Boolean comparison function for implementation *)
Definition lt_custom_bool (a b : N) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if ones_a <? ones_b then true
  else if ones_a =? ones_b then a <? b
  else false.

(* Insertion sort insert function *)
Fixpoint insert_sorted (x : N) (l : list N) : list N :=
  match l with
  | [] => [x]
  | h :: t =>
      if lt_custom_bool x h then
        x :: l
      else
        h :: insert_sorted x t
  end.

(* Main sort implementation *)
Fixpoint sort_array_impl (input : list N) : list N :=
  match input with
  | [] => []
  | h :: t => insert_sorted h (sort_array_impl t)
  end.

(* Specification definition *)
Definition problem_116_spec (input output : list N) : Prop :=
  output = sort_array_impl input.

(* Test case proof *)
Example test_problem_116 :
  problem_116_spec [15; 0; 10101010; 0; 100000] [0; 0; 15; 100000; 10101010].
Proof.
  (* Unfold the specification *)
  unfold problem_116_spec.
  (* Compute the function application and check equality *)
  (* vm_compute is required for performance with large numbers *)
  vm_compute.
  reflexivity.
Qed.