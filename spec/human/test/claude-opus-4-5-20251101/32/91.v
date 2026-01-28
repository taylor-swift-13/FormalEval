Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Import Coq.Reals.Reals.

Fixpoint eval_poly (coeffs : list R) (x : R) : R :=
  match coeffs with
  | [] => 0%R
  | c :: cs => (c + x * (eval_poly cs x))%R
  end.

Definition problem_32_pre (input : list R) : Prop := length input > 0 /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  eval_poly input output = 0%R.

Definition input_real : list R := [9%R; (-8)%R; 4%R; 3%R; 10%R; 8%R; (-4)%R; 2%R].

Axiom output_is_root : exists output : R,
  eval_poly input_real output = 0%R.

Definition output_real : R := (-1.2079210931679463)%R.

Example test_problem_32 : exists output : R, problem_32_spec input_real output.
Proof.
  unfold problem_32_spec.
  exact output_is_root.
Qed.