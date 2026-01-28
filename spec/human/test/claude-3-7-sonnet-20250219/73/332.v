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
    [-10%Z; -9%Z; -8%Z; -7%Z; -6%Z; -5%Z; 17%Z; -4%Z; -3%Z; -2%Z; 17%Z; -1%Z; -1%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 16%Z; 7%Z; 8%Z; -7%Z; 9%Z; 10%Z; -9%Z]
    12%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 26 *)
  (* half_len = 13 *)
  (* first_half = firstn 13 arr 
       = [-10; -9; -8; -7; -6; -5; 17; -4; -3; -2; 17; -1; -1] *)
  (* second_half = skipn (26 - 13) arr = skipn 13 arr
       = [1; 2; 3; 4; 5; 6; 16; 7; 8; -7; 9; 10; -9] *)
  (* rev second_half = [-9; 10; 9; -7; 8; 7; 16; 6; 5; 4; 3; 2; 1] *)
  (* count_diff first_half rev(second_half) 0:
       compare elements pairwise:
       -10 vs -9  -> diff acc=1
       -9 vs 10   -> diff acc=2
       -8 vs 9    -> diff acc=3
       -7 vs -7   -> same acc=3
       -6 vs 8    -> diff acc=4
       -5 vs 7    -> diff acc=5
       17 vs 16   -> diff acc=6
       -4 vs 6    -> diff acc=7
       -3 vs 5    -> diff acc=8
       -2 vs 4    -> diff acc=9
       17 vs 3    -> diff acc=10
       -1 vs 2    -> diff acc=11
       -1 vs 1    -> diff acc=12
  *)
  reflexivity.
Qed.