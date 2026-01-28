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

Definition lt_custom (a b : nat) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

Definition lt_custom_bool (a b : nat) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if Nat.ltb ones_a ones_b then true
  else if Nat.eqb ones_a ones_b then Nat.ltb a b
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

Fixpoint count_ones_Z_helper (n : Z) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if Z.eqb n 0 then 0
      else
        let rest := count_ones_Z_helper (Z.div2 n) fuel' in
        if Z.odd n then S rest else rest
  end.

Definition count_ones_Z (n : Z) : nat :=
  let m := Z.abs n in
  let fuel := (Z.to_nat (Z.log2 (Z.max 1 m)) + 2)%nat in
  count_ones_Z_helper m fuel.

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

Fixpoint sort_array_Z_impl (input : list Z) : list Z :=
  match input with
  | [] => []
  | h :: t => insert_sorted_Z h (sort_array_Z_impl t)
  end.

Definition sort_array_Z (l : list Z) : list Z :=
  sort_array_Z_impl l.

Example problem_116_test_Z :
  sort_array_Z [2097151%Z; 16777215%Z; 2097152%Z; 33554431%Z; 268435455%Z] =
  [2097152%Z; 2097151%Z; 16777215%Z; 33554431%Z; 268435455%Z].
Proof.
  vm_compute.
  reflexivity.
Qed.