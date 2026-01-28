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

Definition x_val : R := 1.6679422344071086.

Example test_problem_32 :
  problem_32_spec [IZR (-3); IZR (-6); IZR (-7); IZR 7] x_val.
Proof.
  unfold problem_32_spec.
  assert (H: 0 = IZR (-3) + x_val * (IZR (-6) + x_val * (IZR (-7) + x_val * (IZR 7 + x_val * 0)))).
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