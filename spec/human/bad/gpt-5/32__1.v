Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.

Local Open Scope R_scope.
Local Open Scope Z_scope.

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
Definition problem_32_pre (input : list R) : Prop := (length input > 0)%nat /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  (* 后置条件: 0 必须是多项式的一个根。*)
  EvalPolyPred input output 0.

Example problem_32_example :
  let input := [IZR (-10%Z); IZR (-2%Z)] in
  let output := (-5)%R in
  problem_32_pre input /\ problem_32_spec input output.
Proof.
  simpl.
  split.
  - split.
    + simpl. lia.
    + simpl. exists 1%nat. reflexivity.
  - unfold problem_32_spec.
    replace 0%R with (IZR (-10%Z) + (-5)%R * (IZR (-2%Z) + (-5)%R * 0%R))%R by lra.
    apply eval_poly_cons.
    apply eval_poly_cons.
    apply eval_poly_nil.
Qed.