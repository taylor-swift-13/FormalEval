Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Local Open Scope Z_scope.

(* Helper function with fuel to ensure termination for structural recursion *)
Fixpoint count_ones_helper (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0 
  | S fuel' => 
      if n =? 0 then 0 
      else (n mod 2) + count_ones_helper (n / 2) fuel' 
  end.

(* Main function using constant fuel sufficient for input size *)
Definition count_ones (n : Z) : Z :=
  count_ones_helper n 100%nat.

(* Comparison logic definition *)
Definition lt_custom (a b : Z) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

(* Boolean comparison function for implementation *)
Definition lt_custom_bool (a b : Z) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if ones_a <? ones_b then true
  else if ones_a =? ones_b then a <? b
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
  problem_116_spec [524287; 16777215; 33554431; 0; 134217728; 134217727; 134217727] 
                   [0; 134217728; 524287; 16777215; 33554431; 134217727; 134217727].
Proof.
  (* Unfold the specification *)
  unfold problem_116_spec.
  (* Compute the function application and check equality *)
  vm_compute.
  reflexivity.
Qed.