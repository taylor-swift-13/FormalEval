Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [3.7763622848915785; 550.123], output = 1038.7318746257051 *)
Example problem_45_test : problem_45_spec 3.7763622848915785 550.123 (3.7763622848915785 * 550.123 / 2).
Proof.
  unfold problem_45_spec.
  lra.
Qed.