(* Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
Examples
solution([5, 8, 7, 1]) ==> 12
solution([3, 3, 3, 3, 3]) ==> 9
solution([30, 13, 24, 321]) ==>0*)
Require Import Arith.
Require Import List.
Require Import Bool.
Import ListNotations.

(* 辅助函数，用于计算位于偶数位置的奇数之和 *)
(* index 参数用于追踪当前元素的位置 *)
Fixpoint sum_odd_in_even_pos_aux (l : list nat) (index : nat) : nat :=
  match l with
  | [] => 0
  | h :: t =>
    if (Nat.even index) && (negb (Nat.even h))
    then h + sum_odd_in_even_pos_aux t (index + 1)
    else sum_odd_in_even_pos_aux t (index + 1)
  end.

(* 程序规约 Spec *)
Definition solution_spec (l : list nat) (output : nat) : Prop :=
  l <> [] ->
  output = sum_odd_in_even_pos_aux l 0.