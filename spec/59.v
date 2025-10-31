(* def largest_prime_factor(n: int):
"""Return the largest prime factor of n. Assume n > 1 and is not a prime.
>>> largest_prime_factor(13195)
29
>>> largest_prime_factor(2048)
2
""" *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory. (* 正确的库，其中定义了 prime *)

(*
 * largest_prime_factor 函数的最终正确程序规约
 *)
Definition largest_prime_factor_spec (n p: Z) : Prop :=
  (* 前置条件: n > 1 并且 n 不是素数 *)
  (Z.gt n 1 /\ ~ (prime n)) ->

  (* 后置条件: p 必须是 n 的最大素数因子 *)
  (
    (* 1. p 是 n 的一个素数因子 *)
    prime p /\ (p | n) /\

    (* 2. p 是最大的那一个 *)
    (* 对于任何其他的素数因子 q，q 都必须小于或等于 p *)
    (forall q: Z, (prime q /\ (q | n)) -> Z.le q p)
  ).