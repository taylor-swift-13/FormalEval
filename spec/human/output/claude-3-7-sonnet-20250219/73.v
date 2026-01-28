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
  problem_73_spec [1%Z; 2%Z; 3%Z; 5%Z; 4%Z; 7%Z; 9%Z; 6%Z] 4%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 8 *)
  (* half_len = 4 *)
  (* first_half = firstn 4 [1;2;3;5;4;7;9;6] = [1;2;3;5] *)
  (* second_half = skipn (8 - 4) arr = skipn 4 arr = [4;7;9;6] *)
  (* rev second_half = [6;9;7;4] *)
  (* count_diff [1;2;3;5] [6;9;7;4] 0 *)
  (* Compare elements: 1 vs 6 -> diff, acc=1 *)
  (* 2 vs 9 -> diff, acc=2 *)
  (* 3 vs 7 -> diff, acc=3 *)
  (* 5 vs 4 -> diff, acc=4 *)
  (* Result = 4 *)
  reflexivity.
Qed.