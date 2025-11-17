(* def smallest_change(arr):
Given an array arr of integers, find the minimum number of elements that
need to be changed to make the array palindromic. A palindromic array is an array that
is read the same backwards and forwards. In one change, you can change one element to any other element.

For example:
smallest_change([1,2,3,5,4,7,9,6]) == 4
smallest_change([1, 2, 3, 4, 3, 2, 2]) == 1
smallest_change([1, 2, 3, 2, 1]) == 0*)

Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

(*
  count_diff l1 l2 acc := 计算 l1 和 l2 之间不同元素的数量
*)
Fixpoint count_diff (l1 l2: list nat) (acc: nat): nat :=
  match l1, l2 with
  | [], _ => acc
  | _, [] => acc
  | h1 :: t1, h2 :: t2 =>
    if Nat.eqb h1 h2 then
      count_diff t1 t2 acc
    else
      count_diff t1 t2 (S acc)
  end.

Definition smallest_change_impl (arr: list nat): nat :=
  let len := length arr in
  let half_len := len / 2 in
  let first_half := firstn half_len arr in
  (* 使用 skipn 来获取列表的后半部分 *)
  let second_half := skipn (len - half_len) arr in
  count_diff first_half (rev second_half) 0.

Definition Pre (arr : list nat) : Prop := True.

Definition smallest_change_spec (arr: list nat) (n: nat): Prop :=
  n = smallest_change_impl arr.