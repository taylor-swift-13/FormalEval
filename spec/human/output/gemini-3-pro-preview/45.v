Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [5; 3], output = 7.5 *)
(* 7.5 is represented as 15/2 in R *)
Example problem_45_test : problem_45_spec 5 3 (15/2).
Proof.
  unfold problem_45_spec.
  lra.
Qed.