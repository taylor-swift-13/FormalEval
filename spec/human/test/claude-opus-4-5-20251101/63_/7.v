(* 引入Coq中关于自然数的基础库 *)
Require Import Coq.Init.Nat.

(*
  is_fibfib n res 是一个归纳定义的命题，它断言 "res 是第 n 个 FibFib 数"。
  这个定义直接从 fibfib 函数的数学定义翻译而来。
*)
Inductive is_fibfib : nat -> nat -> Prop :=
  (* Base Case 1: 第 0 个 FibFib 数是 0 *)
  | ff_zero : is_fibfib 0 0

  (* Base Case 2: 第 1 个 FibFib 数是 0 *)
  | ff_one  : is_fibfib 1 0

  (* Base Case 3: 第 2 个 FibFib 数是 1 *)
  | ff_two  : is_fibfib 2 1

  (*
    Inductive Step: 归纳步骤。
    如果 res_n, res_n1, res_n2 分别是第 n, n+1, n+2 个 FibFib 数，
    那么第 n+3 个 FibFib 数就是它们三者的和。
  *)
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.
(*
  problem_63_spec 是对 fibfib 函数的程序规约。

  它指出，一个函数若要满足此规约，其对于任何输入 n，
  必须返回一个结果 res，使得 is_fibfib n res 命题为真。

  参数：
  - n: nat    (代表程序的输入)
  - res: nat  (代表程序的输出)
*)
Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

(* Test case: input = 14, output = 927 *)
Example test_fibfib_14 : problem_63_spec 14 927.
Proof.
  unfold problem_63_spec.
  assert (H0: is_fibfib 0 0) by apply ff_zero.
  assert (H1: is_fibfib 1 0) by apply ff_one.
  assert (H2: is_fibfib 2 1) by apply ff_two.
  assert (H3: is_fibfib 3 1) by (apply (ff_step 0 0 0 1); assumption).
  assert (H4: is_fibfib 4 2) by (apply (ff_step 1 0 1 1); assumption).
  assert (H5: is_fibfib 5 4) by (apply (ff_step 2 1 1 2); assumption).
  assert (H6: is_fibfib 6 7) by (apply (ff_step 3 1 2 4); assumption).
  assert (H7: is_fibfib 7 13) by (apply (ff_step 4 2 4 7); assumption).
  assert (H8: is_fibfib 8 24) by (apply (ff_step 5 4 7 13); assumption).
  assert (H9: is_fibfib 9 44) by (apply (ff_step 6 7 13 24); assumption).
  assert (H10: is_fibfib 10 81) by (apply (ff_step 7 13 24 44); assumption).
  assert (H11: is_fibfib 11 149) by (apply (ff_step 8 24 44 81); assumption).
  assert (H12: is_fibfib 12 274) by (apply (ff_step 9 44 81 149); assumption).
  assert (H13: is_fibfib 13 504) by (apply (ff_step 10 81 149 274); assumption).
  apply (ff_step 11 149 274 504); assumption.
Qed.