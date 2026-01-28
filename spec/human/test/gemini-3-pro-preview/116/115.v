Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

(* Helper function to count ones in a positive number (binary representation) *)
Fixpoint count_ones_pos (p : positive) : Z :=
  match p with
  | xH => 1
  | xO p' => count_ones_pos p'
  | xI p' => 1 + count_ones_pos p'
  end.

(* Main function to count ones in Z *)
Definition count_ones (n : Z) : Z :=
  match n with
  | 0 => 0
  | Z.pos p => count_ones_pos p
  | Z.neg p => count_ones_pos p
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
  problem_116_spec [2097151; 524287; 16777215; 33554431; 0; 134217727; 134217727] 
                   [0; 524287; 2097151; 16777215; 33554431; 134217727; 134217727].
Proof.
  (* Unfold the specification *)
  unfold problem_116_spec.
  (* Use vm_compute for efficient calculation with large integers *)
  vm_compute.
  (* Check equality *)
  reflexivity.
Qed.