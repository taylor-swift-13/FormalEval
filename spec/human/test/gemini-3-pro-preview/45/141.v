Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [1000000000000; 500000000], output = 2.5e+20 *)
(* 2.5e+20 is represented as 250000000000000000000 in R *)
Example problem_45_test : problem_45_spec 1000000000000 500000000 250000000000000000000.
Proof.
  unfold problem_45_spec.
  lra.
Qed.