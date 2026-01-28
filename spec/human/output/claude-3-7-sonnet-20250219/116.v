Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Definition of count_ones_helper as given *)
Fixpoint count_ones_helper (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match n with
      | 0 => 0
      | _ => (n mod 2) + count_ones_helper (n / 2) fuel'
      end
  end.

Definition count_ones (n : nat) : nat :=
  count_ones_helper n n.

Definition lt_custom_bool (a b : nat) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if ones_a <? ones_b then true
  else if ones_a =? ones_b then a <? b
  else false.

Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t =>
      if lt_custom_bool x h then
        x :: l
      else
        h :: insert_sorted x t
  end.

Fixpoint sort_array_impl (input : list nat) : list nat :=
  match input with
  | [] => []
  | h :: t => insert_sorted h (sort_array_impl t)
  end.

Definition problem_116_spec (input output : list nat) : Prop :=
  output = sort_array_impl input.

(* Corrected test example with expected output matching sort_array_impl:
   Sort [1;5;2;3;4] according to count_ones ascending then decimal ascending gives
   [1;2;4;3;5]
   Explanation:
   count_ones of:
   1 (binary 1) = 1
   2 (binary 10) = 1
   4 (binary 100) = 1
   3 (binary 11) = 2
   5 (binary 101) = 2
   Sorting by number of ones ascending:
   first 1,2,4 (all 1 one), in ascending numeric order: 1,2,4
   then 3,5 (2 ones), ascending numeric order: 3,5
*)

Example test_sort_array_corrected :
  problem_116_spec [1;5;2;3;4] [1;2;4;3;5].
Proof.
  unfold problem_116_spec.
  simpl.
  reflexivity.
Qed.

(* Additional test case given in problem description for assurance *)

Example test_sort_array_zero :
  problem_116_spec [1;0;2;3;4] [0;1;2;4;3].
Proof.
  unfold problem_116_spec.
  simpl.
  reflexivity.
Qed.