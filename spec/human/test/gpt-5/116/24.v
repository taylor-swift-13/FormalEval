Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Permutation.
Require Import Sorting.Sorted.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Fixpoint count_ones_helper_Z (n : Z) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if Z.eqb n 0 then 0
      else ((if Z.odd n then 1 else 0) + count_ones_helper_Z (Z.div2 n) fuel')
  end.

Definition count_ones_Z (n : Z) : nat :=
  count_ones_helper_Z (Z.abs n) (Z.to_nat (Z.log2 (Z.max 1 (Z.abs n)) + 1)).

Definition lt_custom_Z_bool (a b : Z) : bool :=
  let ones_a := count_ones_Z a in
  let ones_b := count_ones_Z b in
  if Nat.ltb ones_a ones_b then true
  else if Nat.eqb ones_a ones_b then Z.ltb a b
  else false.

Fixpoint insert_sorted_Z (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t =>
      if lt_custom_Z_bool x h then
        x :: l
      else
        h :: insert_sorted_Z x t
  end.

Fixpoint sort_array_impl_Z (input : list Z) : list Z :=
  match input with
  | [] => []
  | h :: t => insert_sorted_Z h (sort_array_impl_Z t)
  end.

Definition problem_116_pre (input : list Z) : Prop := True.

Definition problem_116_spec (input output : list Z) : Prop :=
  output = sort_array_impl_Z input.

Example problem_116_test_Z :
  problem_116_spec [15%Z; 0%Z; 10101010%Z; 0%Z; 100000%Z] [0%Z; 0%Z; 15%Z; 100000%Z; 10101010%Z].
Proof.
  unfold problem_116_spec.
  vm_compute.
  reflexivity.
Qed.