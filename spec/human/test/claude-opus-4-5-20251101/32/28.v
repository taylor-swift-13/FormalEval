Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Import Coq.Reals.Reals.

(*
 * eval_poly coeffs x 计算多项式 coeffs 在点 x 的值
 *)
Fixpoint eval_poly (coeffs : list R) (x : R) : R :=
  match coeffs with
  | [] => 0%R
  | c :: cs => (c + x * (eval_poly cs x))%R
  end.


(* Pre: input list must be non-empty and have even length (as required by Spec) *)
Definition problem_32_pre (input : list R) : Prop := length input > 0 /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  (* 后置条件: 0 必须是多项式的一个根。*)
  eval_poly input output = 0%R.

(* Convert the input from integers to reals *)
Definition input_real : list R := [9%R; 1%R].
Definition output_real : R := (-9)%R.

Example test_problem_32 : problem_32_spec input_real output_real.
Proof.
  unfold problem_32_spec.
  unfold input_real, output_real.
  unfold eval_poly.
  ring.
Qed.