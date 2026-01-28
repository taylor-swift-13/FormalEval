Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

(* Helper function to count ones in positive integers *)
Fixpoint count_ones_pos (p : positive) : Z :=
  match p with
  | xI q => 1 + count_ones_pos q
  | xO q => count_ones_pos q
  | xH => 1
  end.

(* Main function using Z *)
Definition count_ones (n : Z) : Z :=
  match n with
  | Z0 => 0
  | Zpos p => count_ones_pos p
  | Zneg p => count_ones_pos p
  end.

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
  problem_116_spec 
    [9999999; 10000000; 123456789; 1028; 123456789; 777778; 111111111; 444555666; 17; 12312312; 8888; 99999; 9999999]
    [17; 1028; 8888; 10000000; 99999; 777778; 9999999; 9999999; 123456789; 123456789; 444555666; 12312312; 111111111].
Proof.
  unfold problem_116_spec.
  vm_compute.
  reflexivity.
Qed.