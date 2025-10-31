(* def hex_key(num):
"""You have been tasked to write a function that receives
a hexadecimal number as a string and counts the number of hexadecimal
digits that are primes (prime number, or a prime, is a natural number
greater than 1 that is not a product of two smaller natural numbers).
Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
So you have to determine a number of the following digits: 2, 3, 5, 7,
B (=decimal 11), D (=decimal 13).
Note: you may assume the input is always correct or empty string,
and symbols A,B,C,D,E,F are always uppercase.
Examples:
For num = "AB" the output should be 1.
For num = "1077E" the output should be 2.
For num = "ABED1A33" the output should be 4.
For num = "123456789ABCDEF0" the output should be 6.
For num = "2020" the output should be 2.
""" *)
(* 导入所需的库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(*
 * 定义一个辅助断言，用于判断一个字符是否为
 * 代表素数的十六进制数字 (2, 3, 5, 7, B, D)。
 *)
Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char | "B"%char | "D"%char => true
  | _ => false
  end.

(*
 * 定义一个递归函数，用于计算 ASCII 码列表中
 * 满足 is_prime_hex_digit 的字符数量。
 * 这个函数纯粹是规约的一部分，用于清晰地表达逻辑。
 *)
Fixpoint count_prime_hex (l : list ascii) : nat :=
  match l with
  | [] => 0 (* 空列表的结果为 0 *)
  | h :: t => (* 对于非空列表 *)
      (if is_prime_hex_digit h then 1 else 0) + count_prime_hex t
  end.

(*
 * hex_key 程序的程序规约 (Spec)。
 *
 * 它是一个 Prop (命题)，通过一阶逻辑描述了
 * 输入字符串 s 和输出自然数 n 之间的关系。
 *
 * 输入: s - string (输入字符串)
 * 输出: n - nat (输出的计数值)
 *
 * 规约: 输出 n 必须等于输入字符串 s 中
 *       代表素数的十六进制字符的数量。
 *)
Definition hex_key_spec (s : list ascii) (n : nat) : Prop :=
  n = count_prime_hex s.