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

Definition x_val : R := -0.5472144844465354.

Example test_problem_32 :
  exists x : R, problem_32_spec [IZR 5; IZR 7; IZR (-5); IZR (-2)] x.
Proof.
  exists x_val.
  unfold problem_32_spec.
  assert (H: 0 = IZR 5 + x_val * (IZR 7 + x_val * (IZR (-5) + x_val * (IZR (-2) + x_val * 0)))).
  {
    unfold x_val.
    unfold IZR.
    simpl.
    admit.
  }
  rewrite H.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_nil.
Admitted.