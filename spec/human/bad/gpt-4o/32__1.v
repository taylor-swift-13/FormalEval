Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

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

(* Pre: input list must be non-empty and have even length (as required by Spec) *)
Definition problem_32_pre (input : list R) : Prop := length input > 0 /\ exists n, length input = 2 * n.

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  (* 后置条件: 0 必须是多项式的一个根。*)
  EvalPolyPred input output 0.

Example test_case_1 :
  problem_32_spec [-10; -2] (-5.0).
Proof.
  unfold problem_32_spec.
  apply eval_poly_cons with (res_tail := 0).
  - apply eval_poly_nil.
  - simpl. lra.
Qed.