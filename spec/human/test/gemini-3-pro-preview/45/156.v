Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [5.933203128831868; 1000000000000], output corrected to 2966601564415.934 *)
(* Note: The provided output 2966601564415.9336 was inexact. We use the exact value 2966601564415.934 for the proof. *)
Example problem_45_test : problem_45_spec 5.933203128831868 1000000000000 2966601564415.934.
Proof.
  unfold problem_45_spec.
  lra.
Qed.