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
  problem_73_spec [1%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 12%Z] 9%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 19 *)
  (* half_len = 19 / 2 = 9 *)
  (* first_half = firstn 9 arr = [1; 3; 4; 5; 6; 7; 8; 9; 11] *)
  (* second_half = skipn (19 - 9) arr = skipn 10 arr = [13; 14; 15; 16; 17; 18; 19; 20; 12] *)
  (* rev second_half = [12; 20; 19; 18; 17; 16; 15; 14; 13] *)
  (* count_diff [1;3;4;5;6;7;8;9;11] [12;20;19;18;17;16;15;14;13] 0 *)
  (* Compare elements: *)
  (* 1 vs 12 diff acc=1 *)
  (* 3 vs 20 diff acc=2 *)
  (* 4 vs 19 diff acc=3 *)
  (* 5 vs 18 diff acc=4 *)
  (* 6 vs 17 diff acc=5 *)
  (* 7 vs 16 diff acc=6 *)
  (* 8 vs 15 diff acc=7 *)
  (* 9 vs 14 diff acc=8 *)
  (* 11 vs 13 diff acc=9 *)
  reflexivity.
Qed.