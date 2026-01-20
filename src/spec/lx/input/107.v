(* Given a positive integer n, return a tuple that has the number of even and odd
integer palindromes that fall within the range(1, n), inclusive.

Example 1:

Input: 3
Output: (1, 2)
Explanation:
Integer palindrome are 1, 2, 3. one of them is even, and two of them are odd.

Example 2:

Input: 12
Output: (4, 6)
Explanation:
Integer palindrome are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11. four of them are even, and 6 of them are odd.
 *)
 
(* 引入Coq标准库中的自然数和列表模块 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* 确保我们可以使用 nat 上的布尔运算符 *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

(*
  函数：将一个自然数转换为其十进制数字列表（反向）
*)
Fixpoint to_digits_helper (n k : nat) {struct k} : list nat :=
  match k with
  | O => []
  | S k' =>
      match n with
      | O => []
      | S _ => (n mod 10) :: to_digits_helper (n / 10) k'
      end
  end.

Definition to_digits_rev (n : nat) : list nat :=
  to_digits_helper n n.

(*
  辅助函数：比较两个 nat 列表是否相等，返回布尔值。
*)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => andb (h1 =? h2) (list_nat_eqb t1 t2)
  | _, _ => false
  end.

(*
  定义：判断一个自然数是否是回文数
*)
Definition is_palindrome (n : nat) : bool :=
  let digits_rev := to_digits_rev n in
  if (n =? 0)
  then false (* 0 不在 [1,n] 范围内, 但做个防御性定义 *)
  else list_nat_eqb digits_rev (rev digits_rev).

(* 定义：判断一个自然数是否是偶数 *)
Definition is_even (n : nat) : bool :=
  (n mod 2 =? 0).

(* 定义：判断一个数是否是偶数回文数 *)
Definition is_even_palindrome (n : nat) : bool :=
  andb (is_palindrome n) (is_even n).

(* 定义：判断一个数是否是奇数回文数 *)
Definition is_odd_palindrome (n : nat) : bool :=
  andb (is_palindrome n) (negb (is_even n)).

(*
  计数函数：递归地计算在 [1, k] 范围中有多少个数满足谓词 P
*)
Fixpoint count_in_range (P : nat -> bool) (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => (if P (S k') then 1 else 0) + count_in_range P k'
  end.


Definition count_palindromes_spec (n : nat) (res : nat * nat) : Prop :=
  res = (count_in_range is_even_palindrome n, count_in_range is_odd_palindrome n).
  
  