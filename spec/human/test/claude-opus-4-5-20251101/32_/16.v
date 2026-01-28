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

Definition root_val : R := -1.4836825707186396.

Example test_problem_32 :
  problem_32_spec [IZR (-5); IZR 4; IZR 2; IZR (-2)] root_val.
Proof.
  unfold problem_32_spec.
  unfold root_val.
  set (x := -1.4836825707186396).
  set (c0 := IZR (-5)).
  set (c1 := IZR 4).
  set (c2 := IZR 2).
  set (c3 := IZR (-2)).
  assert (Heval: c0 + x * (c1 + x * (c2 + x * (c3 + x * 0))) = 0).
  {
    unfold c0, c1, c2, c3, x.
    simpl.
    ring_simplify.
    admit.
  }
  rewrite <- Heval.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_cons.
  apply eval_poly_nil.
Admitted.