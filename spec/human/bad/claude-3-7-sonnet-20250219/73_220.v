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
  problem_73_spec
    [1%Z; 2%Z; 3%Z; 4%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 13%Z; 26%Z; -3%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 41%Z; 43%Z; 44%Z; 45%Z; 46%Z; 48%Z; 49%Z; 50%Z; 13%Z; 35%Z; 6%Z]
    24%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  remember (length
    [1%Z; 2%Z; 3%Z; 4%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 13%Z; 26%Z; -3%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 41%Z; 43%Z; 44%Z; 45%Z; 46%Z; 48%Z; 49%Z; 50%Z; 13%Z; 35%Z; 6%Z]) as len eqn:Heq_len.
  assert (half_len : nat) by (exact (len / 2)%nat).
  clear Heq_len.
  remember (firstn half_len
    [1%Z; 2%Z; 3%Z; 4%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 13%Z; 26%Z; -3%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 41%Z; 43%Z; 44%Z; 45%Z; 46%Z; 48%Z; 49%Z; 50%Z; 13%Z; 35%Z; 6%Z]) as first_half eqn:Heq_first_half.
  remember (skipn (len - half_len) 
    [1%Z; 2%Z; 3%Z; 4%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 13%Z; 26%Z; -3%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 41%Z; 43%Z; 44%Z; 45%Z; 46%Z; 48%Z; 49%Z; 50%Z; 13%Z; 35%Z; 6%Z]) as second_half eqn:Heq_second_half.
  simpl in *.
  assert (len = 48) by reflexivity; subst len.
  subst half_len.
  (* half_len = 48 / 2 = 24 *)
  subst first_half.
  subst second_half.
  (* first_half = firstn 24 input list *)
  (* second_half = skipn (48 - 24) input list = skipn 24 input list *)
  (* Compute elements to compare *)
  (* first_half = *)
  (* [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 13] *)
  (* second_half = *)
  (* [26; -3; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 41; 43; 44; 45; 46; 48; 49; 50; 13; 35; 6] *)
  (* rev second_half = *)
  (* [6; 35; 13; 50; 49; 48; 46; 45; 44; 43; 41; 39; 38; 37; 36; 35; 34; 33; 32; 31; 30; 29; 28; -3; 26] *)
  (* We only compare first 24 of reversed second_half *)
  (* So list to compare with first_half is [6;35;13;50;49;48;46;45;44;43;41;39;38;37;36;35;34;33;32;31;30;29;28;-3] *)
  (* Count differences: elements at position i compared *)
  (* (1,6), (2,35), (3,13), (4,50), (6,49), (7,48), (8,46), (9,45), (10,44), (11,43), (12,41), (13,39), *)
  (* (14,38), (15,37), (16,36), (17,35), (18,34), (19,33), (20,32), (21,31), (22,30), (23,29), (24,28), (13, -3) *)
  (* Count how many are equal: only the last pair (13,-3) is 13 vs -3 no equal, so 0 matches *)
  (* So result should be 24 *)
  reflexivity.
Qed.