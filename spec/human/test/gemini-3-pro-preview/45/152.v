Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [2.944801050034961; 1000000000000], output = 1472400525017.4805 *)
Example problem_45_test : problem_45_spec 2.944801050034961 1000000000000 1472400525017.4805.
Proof.
  unfold problem_45_spec.
  lra.
Qed.