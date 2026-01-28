Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Sorting.Sorted.
Import ListNotations.

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

Definition lt_custom (a b : nat) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

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

Definition problem_116_pre (input : list nat) : Prop := True.

Definition problem_116_spec (input output : list nat) : Prop :=
  output = sort_array_impl input.

Require Import ZArith.
Open Scope Z_scope.

Definition nat_list_from_Z (l : list Z) : list nat :=
  map Z.to_nat l.

Example test_problem_116 :
  problem_116_spec (nat_list_from_Z [1024; 1025; 1026; 1027; 1028; 1029; 1030; 1031; 1032; 1033]) (nat_list_from_Z [1024; 1025; 1026; 1028; 1032; 1027; 1029; 1030; 1033; 1031]).
Proof.
  unfold problem_116_spec.
  unfold nat_list_from_Z.
  native_compute.
  reflexivity.
Qed.