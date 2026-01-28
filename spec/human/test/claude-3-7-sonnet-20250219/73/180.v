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
  problem_73_spec [1%Z; 2%Z; 3%Z; 34%Z; 4%Z; 5%Z; 4%Z; 3%Z; 4%Z; 5%Z; 4%Z; 4%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 2%Z; 4%Z] 6%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 19 *)
  (* half_len = 9 *)
  (* first_half = firstn 9 [1;2;3;34;4;5;4;3;4;5;4;4;3;4;5;4;3;2;4] = [1;2;3;34;4;5;4;3;4] *)
  (* second_half = skipn (19 - 9) arr = skipn 10 arr 
     = [4;4;3;4;5;4;3;2;4] *)
  (* rev second_half = [4;2;3;4;5;4;3;4;4] *)
  (* Compare elements: *)
  (* 1 vs 4 => diff acc=1 *)
  (* 2 vs 2 => same acc=1 *)
  (* 3 vs 3 => same acc=1 *)
  (* 34 vs 4 => diff acc=2 *)
  (* 4 vs 5 => diff acc=3 *)
  (* 5 vs 4 => diff acc=4 *)
  (* 4 vs 3 => diff acc=5 *)
  (* 3 vs 4 => diff acc=6 *)
  (* 4 vs 4 => same acc=6 *)
  reflexivity.
Qed.