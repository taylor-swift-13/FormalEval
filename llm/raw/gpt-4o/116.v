
Require Import List.
Require Import Arith.
Require Import Omega.

Definition count_ones (n : nat) : nat :=
  length (filter (fun b => b = true) (nat_to_bin n)).

Fixpoint nat_to_bin (n : nat) : list bool :=
  match n with
  | 0 => nil
  | S n' => (Nat.odd n) :: nat_to_bin (Nat.div2 n)
  end.

Definition cmp_spec (x y : nat) : Z :=
  let x1 := count_ones x in
  let y1 := count_ones y in
  if x1 =? y1 then Z.of_nat x - Z.of_nat y
  else Z.of_nat x1 - Z.of_nat y1.

Definition sort_array_spec (arr sorted_arr : list nat) : Prop :=
  Permutation arr sorted_arr /\
  Sorted (fun x y => cmp_spec x y <= 0) sorted_arr.
