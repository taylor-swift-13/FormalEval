(* The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fib4(0) -> 0
fib4(1) -> 0
fib4(2) -> 2
fib4(3) -> 0
fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
Please write a function to efficiently compute the n-th element of the fib4 number sequence. Do not use recursion.
>>> fib4(5)
4
>>> fib4(6)
8
>>> fib4(7)
14 *)

(* 
  Spec(input : int, output : int) :=

​	∃ Fib : list int,
​		Fib[0] = 0 /\ Fib[1] = 0 /\ Fib[2] = 2 /\ Fib[3] = 0 /\
​		∀i ∈ N, i >3 → Fib[i] = Fib[i-1] + Fib[i-2] + Fib[i-3] + Fib[i-4] /\
​		output = Fib[input] *)


Require Import Coq.Arith.Arith.

Definition fib4_spec_existential (input : nat) (output : nat) : Prop :=
  exists (Fib : nat -> nat),
    (* 1. 基本情况 *)
    Fib 0 = 0 /\
    Fib 1 = 0 /\
    Fib 2 = 2 /\
    Fib 3 = 0 /\
    (* 2. 归纳规则 *)
    (forall i : nat, 4 <= i ->
      Fib i = Fib (i - 1) + Fib (i - 2) + Fib (i - 3) + Fib (i - 4)) /\
    (* 3. 与程序输出的关联 *)
    output = Fib input.