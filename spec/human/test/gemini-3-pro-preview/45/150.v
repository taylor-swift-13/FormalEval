Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [2.944801050034961; 1e-50], output = 1.4724005250174806e-50 *)
Example problem_45_test : problem_45_spec 2.944801050034961 (1 / 10^50) (1.4724005250174805 / 10^50).
Proof.
  unfold problem_45_spec.
  lra.
Qed.