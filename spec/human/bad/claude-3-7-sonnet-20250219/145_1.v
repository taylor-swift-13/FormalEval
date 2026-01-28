Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
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
  if Z_ge_dec n 0 then
    sum_digits_pos_fuel (Z.to_nat (Z.abs n) + 1) n
  else
    let npos := Z.abs n in
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
  | h :: t =>
      let '(zx, ix) := x in
      let '(zh, ih) := h in
      let sx := sum_digits zx in let sh := sum_digits zh in
      if Z.ltb sx sh then x :: l
      else if Z.eqb sx sh
           then if Nat.leb ix ih then x :: l else h :: insert_sorted x t
           else h :: insert_sorted x t
  end.

Fixpoint stable_sort (l : list (Z * nat)) : list (Z * nat) :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (stable_sort t)
  end.

Definition order_by_points_impl (l_in : list Z) : list Z :=
  let indexed := combine l_in (seq 0 (length l_in)) in
  let sorted := stable_sort indexed in
  map fst sorted.

Definition problem_145_pre (l_in : list Z) : Prop := True.

Definition problem_145_spec (l_in : list Z) (output : list Z) : Prop :=
  output = order_by_points_impl l_in.

Example test_order_by_points :
  problem_145_spec [1%Z; 11%Z; -1%Z; -11%Z; -12%Z]
                   [-1%Z; -11%Z; 1%Z; -12%Z; 11%Z].
Proof.
  unfold problem_145_spec, order_by_points_impl.

  (* indexed = [(1,0); (11,1); (-1,2); (-11,3); (-12,4)] *)
  remember (combine [1%Z;11%Z;-1%Z;-11%Z;-12%Z] (seq 0 5)) as indexed eqn:Heq.
  simpl in Heq.
  subst indexed.

  (* Known values of sum_digits *)
  assert (sum_digits 1 = 1).
  {
    unfold sum_digits.
    destruct (Z_ge_dec 1 0).
    - simpl.
      unfold sum_digits_pos_fuel.
      simpl.
      destruct (Z_le_gt_dec 1 0); [lia|].
      simpl.
      destruct (Z_le_gt_dec (1 / 10) 0); [lia|].
      rewrite Z.mod_small with (a:=1)(b:=10); lia.
    - lia.
  }
  assert (sum_digits 11 = 2).
  {
    unfold sum_digits.
    destruct (Z_ge_dec 11 0).
    - simpl.
      unfold sum_digits_pos_fuel.
      simpl.
      destruct (Z_le_gt_dec 11 0); [lia|].
      simpl.
      destruct (Z_le_gt_dec (11 / 10) 0); [lia|].
      rewrite Z.mod_small with (a:=11)(b:=10); lia.
      rewrite Z.mod_small with (a:=1)(b:=10); lia.
    - lia.
  }
  assert (sum_digits (-1) = -1).
  {
    unfold sum_digits.
    destruct (Z_ge_dec (-1) 0).
    - lia.
    - simpl.
      unfold sum_digits_pos_fuel.
      simpl.
      destruct (Z_le_gt_dec 1 0); [lia|].
      simpl.
      destruct (Z_le_gt_dec (1 / 10) 0); [lia|].
      rewrite Z.mod_small with (a:=1)(b:=10); lia.
      unfold msd_fuel.
      simpl.
      destruct (Z_lt_le_dec 1 10); lia.
  }
  assert (sum_digits (-11) = 0).
  {
    unfold sum_digits.
    destruct (Z_ge_dec (-11) 0).
    - lia.
    - simpl.
      unfold sum_digits_pos_fuel.
      simpl.
      destruct (Z_le_gt_dec 11 0); [lia|].
      simpl.
      destruct (Z_le_gt_dec (11 / 10) 0); [lia|].
      rewrite Z.mod_small with (a:=11)(b:=10); lia.
      rewrite Z.mod_small with (a:=1)(b:=10); lia.
      unfold msd_fuel.
      simpl.
      destruct (Z_lt_le_dec 11 10); [lia|].
      destruct (Z_lt_le_dec 1 10); lia.
  }
  assert (sum_digits (-12) = 1).
  {
    unfold sum_digits.
    destruct (Z_ge_dec (-12) 0).
    - lia.
    - simpl.
      unfold sum_digits_pos_fuel.
      simpl.
      destruct (Z_le_gt_dec 12 0); [lia|].
      simpl.
      destruct (Z_le_gt_dec (12 / 10) 0); [lia|].
      rewrite Z.mod_small with (a:=12)(b:=10); lia.
      rewrite Z.mod_small with (a:=1)(b:=10); lia.
      unfold msd_fuel.
      simpl.
      destruct (Z_lt_le_dec 12 10); [lia|].
      destruct (Z_lt_le_dec 1 10); lia.
  }

  (* Now stable_sort [(1,0);(11,1);(-1,2);(-11,3);(-12,4)] *)
  (* Step by step sort *)

  (* stable_sort [(11,1); (-1,2); (-11,3); (-12,4)] *)
  remember (stable_sort [(11,1); (-1,2); (-11,3); (-12,4)]) as s1.

  (* stable_sort [( -1, 2); (-11, 3); (-12, 4) ] *)
  remember (stable_sort [(-1,2); (-11,3); (-12,4)]) as s2.

  (* stable_sort [ (-11,3); (-12,4) ] *)
  remember (stable_sort [(-11,3); (-12,4)]) as s3.

  (* stable_sort [(-12,4)] = [(-12,4)] *)
  simpl in Heqs3.
  inversion Heqs3; subst s3.

  (* insert_sorted (-11,3) [(-12,4)] *)
  simpl.
  unfold insert_sorted.
  rewrite sum_digits_neg11.
  rewrite sum_digits_neg12.
  simpl.
  (* Compare 0 < 1 = true *)
  simpl.
  reflexivity.

  (* So s3 = [(-11,3); (-12,4)] *)

  subst s3.

  (* insert_sorted (-1,2) [(-11,3); (-12,4)] *)
  simpl.
  unfold insert_sorted.
  rewrite sum_digits_neg1.
  rewrite sum_digits_neg11.
  simpl.
  (* Compare -1 < 0 = true *)
  simpl.
  reflexivity.

  subst s2.

  (* So s2 = [(-1,2); (-11,3); (-12,4)] *)

  (* insert_sorted (11,1) s2 *)
  simpl.
  unfold insert_sorted.
  rewrite sum_digits_11.
  rewrite sum_digits_neg1.
  rewrite sum_digits_neg11.
  rewrite sum_digits_neg12.
  simpl.
  (* Compare 2 < -1 -> false *)
  (* 2 == -1? false *)
  (* Else continue to tail *)
  (* Compare 2 < 0 -> false *)
  (* 2 == 0? false *)
  (* Continue tail *)
  (* Compare 2 < 1 -> false *)
  (* 2 == 1? false *)
  (* Continue tail *)
  (* insert_sorted (11,1) [] = [(11,1)] *)
  simpl.
  reflexivity.

  subst s1.

  (* s1 = [(-1,2); (-11,3); (-12,4); (11,1)] *)

  (* insert_sorted (1,0) s1 *)
  simpl.
  unfold insert_sorted.
  rewrite sum_digits_1.
  rewrite sum_digits_neg1.
  rewrite sum_digits_neg11.
  rewrite sum_digits_neg12.
  simpl.
  (* Compare 1 < -1 -> false *)
  (* 1 == -1? false *)
  (* else continue *)
  (* Compare 1 < 0 -> false *)
  (* 1 == 0? false *)
  (* else continue *)
  (* Compare 1 < 1 -> false *)
  (* 1 == 1? true *)
  (* compare indices 0 <= 4 true *)
  simpl.
  reflexivity.

  (* Final sorted list is:
     [(-1,2); (-11,3); (1,0); (-12,4); (11,1)] *)

  (* map fst this list = [-1; -11; 1; -12; 11] *)

  reflexivity.
Qed.