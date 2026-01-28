Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import Arith.
Import ListNotations.
Open Scope Z_scope.


Fixpoint sum_digits_pos_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if Z_le_gt_dec n 0 then 0 else (n mod 10) + sum_digits_pos_fuel f (n / 10)
  end.

Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10
  | S f => if Z_lt_le_dec n 10 then n else msd_fuel f (n / 10)
  end.

Definition sum_digits (n : Z) : Z :=
  if Z_ge_dec n 0 then sum_digits_pos_fuel (Z.to_nat n + 1) n
  else let npos := - n in
       let tot := sum_digits_pos_fuel (Z.to_nat npos + 1) npos in
       let fd := msd_fuel (Z.to_nat npos + 1) npos in
       tot - 2 * fd.

Definition le_stable (p1 p2 : Z * nat) : Prop :=
  let (z1, i1) := p1 in
  let (z2, i2) := p2 in
  let s1 := sum_digits z1 in
  let s2 := sum_digits z2 in
  s1 < s2 \/ (s1 = s2 /\ (i1 <= i2)%nat).

Fixpoint insert_sorted (x : Z * nat) (l : list (Z * nat)) : list (Z * nat) :=
  match l with
  | [] => [x]
  | h :: t => let '(zx, ix) := x in let '(zh, ih) := h in
              let sx := sum_digits zx in let sh := sum_digits zh in
              if Z.ltb sx sh then x :: l
              else if Z.eqb sx sh then if Nat.leb ix ih then x :: l else h :: insert_sorted x t
              else h :: insert_sorted x t
  end.

Fixpoint stable_sort (l : list (Z * nat)) : list (Z * nat) :=
  match l with [] => [] | h :: t => insert_sorted h (stable_sort t) end.

Definition order_by_points_impl (l_in : list Z) : list Z :=
  let indexed := combine l_in (seq 0 (length l_in)) in
  let sorted := stable_sort indexed in
  map fst sorted.

Definition problem_145_pre (l_in : list Z) : Prop := True.

Definition problem_145_spec (l_in : list Z) (output : list Z) : Prop :=
  output = order_by_points_impl l_in.

Example test_order_by_points :
  problem_145_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; -53622%Z; 9%Z; 10%Z; 11%Z; -12%Z; -13%Z; -14%Z; -15%Z; -16%Z; -17%Z; -18%Z; -19%Z; -20%Z; -21%Z; 2%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; -32%Z; -33%Z; -34%Z; -35%Z; -36%Z; -37%Z; -38%Z; -39%Z; -40%Z; -41%Z; 42%Z; 43%Z; 44%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z] [-40%Z; -41%Z; -20%Z; -21%Z; -32%Z; -33%Z; 1%Z; 10%Z; -12%Z; -34%Z; 2%Z; 11%Z; -13%Z; 2%Z; -35%Z; 3%Z; -14%Z; 30%Z; -36%Z; 4%Z; -15%Z; 22%Z; 31%Z; -37%Z; 5%Z; -16%Z; 23%Z; -38%Z; 50%Z; 6%Z; -17%Z; 24%Z; -39%Z; 42%Z; 7%Z; -18%Z; 25%Z; 43%Z; -53622%Z; -19%Z; 26%Z; 44%Z; 9%Z; 27%Z; 28%Z; 46%Z; 29%Z; 47%Z; 48%Z; 49%Z].
Proof.
  unfold problem_145_spec.
  native_compute.
  reflexivity.
Qed.