Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

Example test_problem_45 : problem_45_spec 3.0140143224731513 3.0140143224731513 4.542141168036644.
Proof.
  unfold problem_45_spec.
  unfold Rdiv.
  ring_simplify.
Abort.

Example test_problem_45 : exists output, problem_45_spec 3.0140143224731513 3.0140143224731513 output.
Proof.
  exists (3.0140143224731513 * 3.0140143224731513 / 2).
  unfold problem_45_spec.
  reflexivity.
Qed.