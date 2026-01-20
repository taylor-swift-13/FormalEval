(* def search(lst):
'''
You are given a non-empty list of positive integers. Return the greatest integer that is greater than
zero, and has a frequency greater than or equal to the value of the integer itself.
The frequency of an integer is the number of times it appears in the list.
If no such a value exist, return -1.
Examples:
search([4, 1, 2, 2, 3, 1]) == 2
search([1, 2, 2, 3, 3, 3, 4, 4, 4]) == 3
search([5, 5, 4, 4, 4]) == -1 *)
Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.
Fixpoint count (z : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eqb z h then 1 else 0) + count z t
  end.

Definition search_spec (lst : list Z) (y : Z) : Prop :=
  ~(lst = []) /\ Forall (fun x => x > 0) lst ->

  ( (* 情况一：函数返回 -1 *)
    (* 使用 (-1)%Z 明确指定 -1 的类型为 Z *)
    y = (-1)%Z /\ (forall x, In x lst -> Z.of_nat (count x lst) < x)
  )
  \/
  ( (* 情况二：函数返回一个正整数 y *)
    In y lst /\
    (Z.of_nat (count y lst)) >= y /\
    (forall z, In z lst -> (Z.of_nat (count y lst)) >= z -> z <= y)
  ).