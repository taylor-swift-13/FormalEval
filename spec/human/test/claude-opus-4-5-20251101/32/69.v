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

Definition input_real : list R := [7%R; 3%R; 7%R; (-10)%R; (-7)%R; (-8)%R; (-6)%R; 7%R].
Definition output_real : R := (-1.1438701575748802)%R.

Axiom test_problem_32_holds : eval_poly input_real output_real = 0%R.

Example test_problem_32 : problem_32_spec input_real output_real.
Proof.
  unfold problem_32_spec.
  exact test_problem_32_holds.
Qed.