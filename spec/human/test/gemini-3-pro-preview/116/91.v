Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

(* Helper function with fuel to ensure termination for structural recursion *)
Fixpoint count_ones_helper (n : Z) (fuel : nat) : Z :=
  match fuel with
  | 0%nat => 0 
  | S fuel' => 
      match n with
      | 0 => 0 
      | _ => (n mod 2) + count_ones_helper (n / 2) fuel' 
      end
  end.

(* Main function using fixed sufficient fuel *)
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
  problem_116_spec [2097151; 524287; 16777215; 33554431; 134217727; 134217727] 
                   [524287; 2097151; 16777215; 33554431; 134217727; 134217727].
Proof.
  (* Unfold the specification *)
  unfold problem_116_spec.
  (* Compute the function application and check equality *)
  (* reflexivity automatically normalizes the terms and checks for syntactic equality *)
  reflexivity.
Qed.