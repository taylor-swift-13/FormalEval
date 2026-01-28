Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [304.7017291578964; 1e+50], output = 1.5235086457894822e+52 *)
Example problem_45_test : problem_45_spec 304.7017291578964 (10^50) (1.523508645789482 * 10^52).
Proof.
  unfold problem_45_spec.
  lra.
Qed.