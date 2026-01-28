Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [10.5; 3.5], output = 18.375 *)
(* 10.5 is 21/2, 3.5 is 7/2, 18.375 is 147/8 *)
Example problem_45_test : problem_45_spec (21/2) (7/2) (147/8).
Proof.
  unfold problem_45_spec.
  lra.
Qed.