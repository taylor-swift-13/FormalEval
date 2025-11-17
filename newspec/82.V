(* def prime_length(string):
"""Write a function that takes a string and returns True if the string
length is a prime number or False otherwise
Examples
prime_length('Hello') == True
prime_length('abcdcba') == True
prime_length('kittens') == True
prime_length('orange') == False
""" *)
(* 导入 Coq 标准库，用于字符串和自然数算术 *)
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

(*
 * is_prime n
 * 
 * 描述：这是一个断言（Prop），用于表达自然数 n 是一个素数。
 * 定义：n 是素数，当且仅当 n > 1 且对于所有在 1 和 n 之间的数 d，d 都不能整除 n。
 *)
Definition is_prime (n : nat) : Prop :=
  (1 < n) /\ (forall d, (1 < d) -> (d < n) -> (n mod d <> 0)).

Definition Pre (s : string) : Prop := True.
(*
 * prime_length_spec s b
 * 
 * 描述：这是 prime_length 函数的程序规约。
 *      它关联了输入字符串 s 和输出布尔值 b。
 * 定义：
 * - 如果 s 的长度是一个素数（根据 is_prime 的定义），
 *   那么输出 b 必须为 true。
 * - 否则（如果 s 的长度不是素数），
 *   输出 b 必须为 false。
 *)
Definition prime_length_spec (s : string) (b : bool) : Prop :=
  b = true <-> is_prime (length s).



