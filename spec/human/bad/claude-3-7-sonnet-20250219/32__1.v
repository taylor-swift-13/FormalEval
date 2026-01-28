Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
Import ListNotations.
Local Open Scope R_scope.

(* Inductive predicate defining polynomial evaluation by Horner's method *)
Inductive EvalPolyPred : list R -> R -> R -> Prop :=
  | eval_poly_nil : forall x : R,
      EvalPolyPred [] x 0
  | eval_poly_cons : forall (c : R) (cs : list R) (x res_tail : R),
      EvalPolyPred cs x res_tail ->
      EvalPolyPred (c :: cs) x (c + x * res_tail).

(* Precondition: input list nonempty and with even length *)
Definition problem_32_pre (input : list R) : Prop :=
  length input > 0 /\ Nat.Even (length input).

(* Specification: output is root of polynomial input *)
Definition problem_32_spec (input : list R) (output : R) : Prop :=
  EvalPolyPred input output 0.

(* Test case *)
Example test_case :
  problem_32_spec [-10; -2] (-5).
Proof.
  unfold problem_32_spec.
  (* Goal: EvalPolyPred [-10; -2] (-5) 0 *)
  (* By eval_poly_cons, need EvalPolyPred [-2] (-5) res_tail where 0 = -10 + (-5)*res_tail *)
  (* So res_tail = 2 *)
  remember 2 as res_tail.
  replace 0 with (-10 + (-5)*res_tail) by (subst; lra).
  apply eval_poly_cons.
  (* Goal: EvalPolyPred [-2] (-5) 2 *)
  (* By eval_poly_cons, need EvalPolyPred [] (-5) res_tail_tail where 2 = -2 + (-5)*res_tail_tail *)
  remember (/ -5) as invx.
  exists invx.
  replace 2 with (-2 + (-5)*0) by lra. (* wait, res_tail_tail should be 0 *)

  (* EvalPolyPred [] _ 0 by eval_poly_nil *)
  replace 2 with (-2 + (-5)*0) by lra.
  apply eval_poly_cons.
  apply eval_poly_nil.
Qed.