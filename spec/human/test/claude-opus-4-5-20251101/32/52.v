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

Definition input_real : list R := [(-9)%R; 6%R; (-8)%R; (-5)%R].

Definition output_real : R := 
  let a := (-9)%R in
  let b := 6%R in
  let c := (-8)%R in
  let d := (-5)%R in
  ((-b - sqrt (b*b - 4*a*c)) / (2*a))%R.

Example test_problem_32 : problem_32_spec input_real output_real.
Proof.
  unfold problem_32_spec.
  unfold input_real, output_real.
  unfold eval_poly.
  admit.
Admitted.