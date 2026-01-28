Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

Example problem_45_test : problem_45_spec 11 10 55.
Proof.
  unfold problem_45_spec.
  lra.
Qed.