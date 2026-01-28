Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope R_scope.
Open Scope Z_scope.

(* eval_poly coeffs x 计算多项式 coeffs 在点 x 的值 *)
Fixpoint eval_poly (coeffs : list R) (x : R) : R :=
  match coeffs with
  | [] => 0%R
  | c :: cs => (c + x * (eval_poly cs x))%R
  end.

(* Pre: input list must be non-empty and have even length (as required by Spec) *)
Definition problem_32_pre (input : list R) : Prop := length input > 0 /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  eval_poly input output = 0%R.

Example test_case_1 :
  problem_32_spec [IZR (-10); IZR (-2)] (IZR (-5)).
Proof.
  unfold problem_32_spec.
  simpl.
  (* eval_poly [IZR (-10); IZR (-2)] (IZR (-5)) = -10 + (-5) * (-2) *)
  lra.
Qed.