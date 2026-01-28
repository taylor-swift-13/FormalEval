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

Definition input_real : list R := [1%R; (-20)%R; 156%R; (-864)%R; 2667%R; (-4392)%R; 3744%R; (-1440)%R].
Definition output_real : R := (8765110993608646 / 100000000000000000)%R.

Example test_problem_32 : problem_32_spec input_real output_real.
Proof.
  unfold problem_32_spec.
  unfold input_real, output_real.
  unfold eval_poly.
  admit.
Admitted.