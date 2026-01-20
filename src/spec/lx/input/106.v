(* Implement the function f that takes n as a parameter,
and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even
or the sum of numbers from 1 to i otherwise.
i starts from 1.
the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
Example:
f(5) == [1, 2, 6, 24, 15] *)

(* 引入 Coq 的自然数和列表库 *)
Require Import Nat.
Require Import List.
Import ListNotations.


Fixpoint factorial (i : nat) : nat :=
  match i with
  | 0 => 1
  | S i' => i * factorial i'
  end.


Fixpoint sum_1_to_n (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => i + sum_1_to_n i'
  end.


Definition f_spec (n : nat) (l : list nat) : Prop :=
  (* 规约的核心：l 必须等于一个通过映射生成的列表 *)
  l = map (fun i =>
             (* 问题描述中的索引 i 从 1 开始，而 Coq 的列表索引从 0 开始。*)
             (* 因此，我们使用 (i + 1) 来代表问题描述中的索引。*)
             let problem_index := i + 1 in
             (* 检查索引是偶数还是奇数 *)
             if even problem_index then
               factorial problem_index
             else
               sum_1_to_n problem_index)
          (* (seq 0 n) 会生成一个从 0 到 n-1 的列表: [0; 1; ...; n-1] *)
          (seq 0 n).