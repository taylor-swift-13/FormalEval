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

Example problem_116_test_nat :
  problem_116_spec [1; 5; 2; 3; 4] [1; 2; 4; 3; 5].
Proof.
  unfold problem_116_spec.
  vm_compute.
  reflexivity.
Qed.

Fixpoint count_ones_pos (p : positive) : nat :=
  match p with
  | xH => 1
  | xO p' => count_ones_pos p'
  | xI p' => S (count_ones_pos p')
  end.

Definition count_ones_Z (z : Z) : nat :=
  match z with
  | Z0 => 0
  | Zpos p => count_ones_pos p
  | Zneg _ => 0
  end.

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

Fixpoint sort_array_Z (input : list Z) : list Z :=
  match input with
  | [] => []
  | h :: t => insert_sorted_Z h (sort_array_Z t)
  end.

Example problem_116_test_Z :
  sort_array_Z [100000000%Z; 0%Z; 10101010%Z; 111111111%Z; 100000%Z] =
  [0%Z; 100000%Z; 10101010%Z; 100000000%Z; 111111111%Z].
Proof.
  vm_compute.
  reflexivity.
Qed.