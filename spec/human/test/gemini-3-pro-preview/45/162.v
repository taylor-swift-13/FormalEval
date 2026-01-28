Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

Example problem_45_test : problem_45_spec 3.0140143224731513 1000000000001 1507007161238.08265716123657565.
Proof.
  unfold problem_45_spec.
  lra.
Qed.