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
  problem_73_spec [2%Z; 1%Z; 5%Z; 7%Z; 9%Z; 10%Z; 8%Z; 6%Z; 4%Z; 41%Z; 7%Z] 5%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 11 *)
  (* half_len = 5 *)
  (* first_half = firstn 5 [2;1;5;7;9;10;8;6;4;41;7] = [2;1;5;7;9] *)
  (* second_half = skipn (11 - 5) arr = skipn 6 arr = [8;6;4;41;7] *)
  (* rev second_half = [7;41;4;6;8] *)
  (* count_diff [2;1;5;7;9] [7;41;4;6;8] 0 *)
  (* Compare elements: 2 vs 7 -> diff, acc=1 *)
  (* 1 vs 41 -> diff, acc=2 *)
  (* 5 vs 4 -> diff, acc=3 *)
  (* 7 vs 6 -> diff, acc=4 *)
  (* 9 vs 8 -> diff, acc=5 *)
  (* Result = 5 *)
  reflexivity.
Qed.