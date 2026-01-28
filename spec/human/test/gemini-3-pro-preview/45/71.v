Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [29; 15], output = 217.5 *)
(* 217.5 is represented as 435/2 in R *)
Example problem_45_test : problem_45_spec 29 15 (435/2).
Proof.
  unfold problem_45_spec.
  lra.
Qed.