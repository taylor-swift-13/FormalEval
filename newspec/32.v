(* xs are coefficients of a polynomial.
find_zero find x such that poly(x) = 0.
find_zero returns only only zero point, even if there are many.
Moreover, find_zero only takes list xs having even number of coefficients
and largest non zero coefficient as it guarantees
a solution.
>>> round(find_zero([1, 2]), 2) # f(x) = 1 + 2x
-0.5
>>> round(find_zero([-6, 11, -6, 1]), 2) # (x - 1) * (x - 2) * (x - 3) = -6 + 11x - 6x^2 + x^3
1.0 *)

(*Spec(input : list float, output : float) :=

​	$∑_{i=0}^{n}$ input[i] * output^i = 0

*)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(*
 * EvalPolyPred coeffs x res 为真，当且仅当 "res 是多项式 coeffs 在点 x 的值"
 *)
Inductive EvalPolyPred : list R -> R -> R -> Prop :=
  | eval_poly_nil : forall x : R,
      (* 基本情况: 空多项式的值为 0 *)
      EvalPolyPred [] x 0
  | eval_poly_cons : forall (c : R) (cs : list R) (x res_tail : R),
      (* 归纳步骤: 如果已知列表尾部的评估结果... *)
      EvalPolyPred cs x res_tail ->
      (* ...那么可以断言整个列表的评估结果 *)
      EvalPolyPred (c :: cs) x (c + x * res_tail).

(*
 * 程序规约 Spec (保持不变，但现在依赖于正确的 EvalPolyPred 定义)
 *)
(* Pre: input list must be non-empty and have even length (as required by Spec) *)
Definition Pre (input : list R) : Prop := length input > 0 /\ Nat.Even (length input).

Definition Spec (input : list R) (output : R) : Prop :=
  (* 前提条件: 输入列表的长度必须为正数且为偶数。*)
  length input > 0 /\ Nat.Even (length input) /\
  (* 后置条件: 0 必须是多项式的一个根。*)
  EvalPolyPred input output 0.