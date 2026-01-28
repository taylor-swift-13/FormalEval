Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Permutation.
Require Import Sorting.Sorted.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Definition count_ones_Z (z : Z) : nat :=
  count_ones (Z.to_nat (Z.abs z)).

Definition lt_custom_Z (a b : Z) : Prop :=
  let ones_a := count_ones_Z a in
  let ones_b := count_ones_Z b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ Z.lt a b).

Definition lt_custom_bool_Z (a b : Z) : bool :=
  let ones_a := count_ones_Z a in
  let ones_b := count_ones_Z b in
  if Nat.ltb ones_a ones_b then true
  else if Nat.eqb ones_a ones_b then Z.ltb a b
  else false.

Fixpoint insert_sorted_Z (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t =>
      if lt_custom_bool_Z x h then
        x :: l
      else
        h :: insert_sorted_Z x t
  end.

Fixpoint sort_array_Z (input : list Z) : list Z :=
  match input with
  | [] => []
  | h :: t => insert_sorted_Z h (sort_array_Z t)
  end.

Definition problem_116_pre (input : list Z) : Prop := True.

Definition problem_116_spec (input output : list Z) : Prop :=
  output = sort_array_Z input.

Example problem_116_test_Z :
  problem_116_spec [-2%Z; -3%Z; -4%Z; -5%Z; -6%Z] [-4%Z; -2%Z; -6%Z; -5%Z; -3%Z].
Proof.
  unfold problem_116_spec.
  vm_compute.
  reflexivity.
Qed.