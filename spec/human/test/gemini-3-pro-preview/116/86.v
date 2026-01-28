Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

(* Helper function with fuel to ensure termination for structural recursion *)
Fixpoint count_ones_helper (n : Z) (fuel : nat) : nat :=
  match fuel with
  | 0%nat => 0%nat
  | S fuel' => 
      match n with
      | 0 => 0%nat
      | _ => (if Z.odd n then 1%nat else 0%nat) + count_ones_helper (Z.div2 n) fuel' 
      end
  end.

(* Main function using fixed fuel sufficient for expected input range *)
Definition count_ones (n : Z) : nat :=
  count_ones_helper n 64%nat.

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
  else if (ones_a =? ones_b)%nat then a <? b
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
  problem_116_spec [9999999; 123456789; 987654321; 123456789; 777777; 111111111; 444555666; 1032; 8888; 99999; 9999999] [1032; 8888; 99999; 777777; 9999999; 9999999; 123456789; 123456789; 444555666; 987654321; 111111111].
Proof.
  (* Unfold the specification *)
  unfold problem_116_spec.
  (* Compute the function application and check equality *)
  vm_compute.
  reflexivity.
Qed.