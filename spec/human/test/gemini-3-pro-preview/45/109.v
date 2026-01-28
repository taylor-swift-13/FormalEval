Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [1000.234; 550.123], output = 275125.864391 *)
Example problem_45_test : problem_45_spec (1000234/1000) (550123/1000) (275125864391/1000000).
Proof.
  unfold problem_45_spec.
  lra.
Qed.