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

Definition input_real : list R := [(-1)%R; 7%R; (-6)%R; (-4)%R; 3%R; 2%R; (-5)%R; 9%R].
Definition output_real : R := (1700721777911341 / 10000000000000000)%R.

Example test_problem_32 : problem_32_spec input_real output_real.
Proof.
  unfold problem_32_spec.
  unfold input_real, output_real.
  unfold eval_poly.
  field.
Qed.