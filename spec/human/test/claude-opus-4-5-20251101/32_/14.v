Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope R_scope.

Inductive EvalPolyPred : list R -> R -> R -> Prop :=
  | eval_poly_nil : forall x : R,
      EvalPolyPred [] x 0
  | eval_poly_cons : forall (c : R) (cs : list R) (x res_tail : R),
      EvalPolyPred cs x res_tail ->
      EvalPolyPred (c :: cs) x (c + x * res_tail).

Definition problem_32_pre (input : list R) : Prop := 
  (length input > 0)%nat /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  EvalPolyPred input output 0.

Definition x_val : R := 0.2908351937976529.

Definition poly_result : R :=
  IZR (-2) + x_val * (IZR 4 + x_val * (IZR 10 + x_val * (IZR 1 + x_val * (IZR (-5) + x_val * (IZR 1 + x_val * (IZR 1 + x_val * (IZR (-4) + x_val * 0))))))).

Example test_problem_32 :
  EvalPolyPred [IZR (-2); IZR 4; IZR 10; IZR 1; IZR (-5); IZR 1; IZR 1; IZR (-4)] x_val poly_result.
Proof.
  unfold poly_result, x_val.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_nil.
Qed.