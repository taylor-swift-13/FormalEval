Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

Example test_problem_45 : problem_45_spec 2.5171570275185937 4 5.034314055037187.
Proof.
  unfold problem_45_spec.
  unfold Rdiv.
  ring_simplify.
  reflexivity.
Qed.