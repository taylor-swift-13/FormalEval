(* def count_up_to(n):
"""Implement a function that takes an non-negative integer and returns an array of the first n
integers that are prime numbers and less than n.
for example:
count_up_to(5) => [2,3]
count_up_to(11) => [2,3,5,7]
count_up_to(0) => []
count_up_to(20) => [2,3,5,7,11,13,17,19]
count_up_to(1) => []
count_up_to(18) => [2,3,5,7,11,13,17]
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted. (* 引入 Sorted 定义 *)
Import ListNotations.

(* is_prime 的定义保持不变 *)
Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall n : nat, 1 < n < p -> ~ (n mod p = 0).


Definition count_up_to_spec (n : nat) (result : list nat) : Prop :=
  (* 属性1: 结果列表中的所有元素都是素数 *)
  (forall p, In p result -> is_prime p) /\

  (* 属性2: 结果列表中的所有元素都小于 n *)
  (forall p, In p result -> p < n) /\

  (* 属性3: 所有小于 n 的素数都在结果列表中 (完备性) *)
  (forall p, is_prime p -> p < n -> In p result) /\

  (* 属性4: 列表是严格升序的 *)
  Sorted lt result /\

  (* 属性5: 列表中没有重复元素 *)
  NoDup result.