Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope R_scope.

(*
 * EvalPolyPred coeffs x res 为真，当且仅当 "res 是多项式 coeffs 在点 x 的值"
 *)
Inductive EvalPolyPred : list R -> R -> R -> Prop :=
  | eval_poly_nil : forall x : R,
      EvalPolyPred [] x 0
  | eval_poly_cons : forall (c : R) (cs : list R) (x res_tail : R),
      EvalPolyPred cs x res_tail ->
      EvalPolyPred (c :: cs) x (c + x * res_tail).

(* Pre: input list must be non-empty and have even length (as required by Spec) *)
Definition problem_32_pre (input : list R) : Prop := 
  (length input > 0)%nat /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  EvalPolyPred input output 0.

(* Test case: input = [-10; -2], output = -5.0 *)
(* Polynomial: -10 + (-2)*x = 0 => x = -5 *)
(* Verification: -10 + (-2)*(-5) = -10 + 10 = 0 *)

Example test_problem_32 :
  problem_32_spec [IZR (-10); IZR (-2)] (-5).
Proof.
  unfold problem_32_spec.
  (* We need to show: EvalPolyPred [-10; -2] (-5) 0 *)
  (* That is: -10 + (-5) * (-2 + (-5) * 0) = 0 *)
  (* = -10 + (-5) * (-2) = -10 + 10 = 0 *)
  assert (H: 0 = IZR (-10) + -5 * (IZR (-2) + -5 * 0)) by lra.
  rewrite H.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_nil.
Qed.