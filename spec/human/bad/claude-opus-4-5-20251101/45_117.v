Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

Example test_problem_45 : problem_45_spec 10.5 3.7763622848915785 19.825901995680788.
Proof.
  unfold problem_45_spec.
  unfold Rdiv.
  ring_simplify.
  reflexivity.
Qed.