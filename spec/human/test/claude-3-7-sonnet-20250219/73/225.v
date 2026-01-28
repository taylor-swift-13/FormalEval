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
  problem_73_spec [0%Z; 1%Z; 2%Z; 2%Z; 3%Z; 4%Z; 4%Z; 5%Z; 5%Z; 6%Z; 7%Z; 22%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z] 9%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 19 *)
  (* half_len = 9 *)
  (* first_half = firstn 9 arr = [0;1;2;2;3;4;4;5;5] *)
  (* second_half = skipn (19 - 9) arr = skipn 10 arr = [7;22;7;8;8;9;9;10;10] *)
  (* rev second_half = [10;10;9;9;8;8;7;22;7] *)
  (* count_diff first_half rev_second_half 0 *)
  (* compare element-wise: *)
  (* 0 vs 10 -> diff acc=1 *)
  (* 1 vs 10 -> diff acc=2 *)
  (* 2 vs 9 -> diff acc=3 *)
  (* 2 vs 9 -> diff acc=4 *)
  (* 3 vs 8 -> diff acc=5 *)
  (* 4 vs 8 -> diff acc=6 *)
  (* 4 vs 7 -> diff acc=7 *)
  (* 5 vs 22 -> diff acc=8 *)
  (* 5 vs 7 -> diff acc=9 *)
  reflexivity.
Qed.