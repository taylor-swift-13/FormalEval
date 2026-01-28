Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

(*
  count_diff l1 l2 acc := 计算 l1 和 l2 之间不同元素的数量
*)
Fixpoint count_diff (l1 l2: list Z) (acc: Z): Z :=
  match l1, l2 with
  | [], _ => acc
  | _, [] => acc
  | h1 :: t1, h2 :: t2 =>
    if Z.eqb h1 h2 then
      count_diff t1 t2 acc
    else
      count_diff t1 t2 (Z.succ acc)
  end.

Definition smallest_change_impl (arr: list Z): Z :=
  let len := length arr in
  let half_len := (len / 2)%nat in
  let first_half := firstn half_len arr in
  let second_half := skipn (len - half_len) arr in
  count_diff first_half (rev second_half) 0.

Definition problem_73_pre (arr : list Z) : Prop := True.

Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  n = smallest_change_impl arr.

Example test_smallest_change_1 :
  problem_73_spec [1%Z; 2%Z; 46%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 49%Z; 9%Z; 7%Z; 10%Z; 10%Z; 9%Z; 8%Z; 38%Z; 7%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 10%Z; 6%Z] 12%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 25 *)
  (* half_len = 25 / 2 = 12 *)
  (* first_half = firstn 12 arr = [1; 2; 46; 3; 4; 5; 6; 7; 49; 9; 7; 10] *)
  (* second_half = skipn (25 - 12) arr = skipn 13 arr = [9; 8; 38; 7; 6; 5; 4; 3; 2; 1; 10; 6] *)
  (* rev second_half = [6; 10; 1; 2; 3; 4; 5; 6; 7; 38; 8; 9] *)
  (* Compare elements pairwise: *)
  (*  1 vs 6 -> diff, acc = 1 *)
  (*  2 vs 10 -> diff, acc = 2 *)
  (* 46 vs 1 -> diff, acc = 3 *)
  (*  3 vs 2 -> diff, acc = 4 *)
  (*  4 vs 3 -> diff, acc = 5 *)
  (*  5 vs 4 -> diff, acc = 6 *)
  (*  6 vs 5 -> diff, acc = 7 *)
  (*  7 vs 6 -> diff, acc = 8 *)
  (* 49 vs 7 -> diff, acc = 9 *)
  (*  9 vs 38 -> diff, acc = 10 *)
  (*  7 vs 8 -> diff, acc = 11 *)
  (* 10 vs 9 -> diff, acc = 12 *)
  reflexivity.
Qed.