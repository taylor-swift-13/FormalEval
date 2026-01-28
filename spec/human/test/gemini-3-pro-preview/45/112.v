Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [1e+50; 1e-50], output = 0.5 *)
Example problem_45_test : problem_45_spec (10^50) (/ 10^50) 0.5.
Proof.
  unfold problem_45_spec.
  rewrite Rinv_r.
  - lra.
  - apply pow_nonzero.
    lra.
Qed.