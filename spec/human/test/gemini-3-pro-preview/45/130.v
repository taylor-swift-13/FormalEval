Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [6.351228473089266e-51; 1e+50], output = 0.3175614236544633 *)
Example problem_45_test : problem_45_spec (6351228473089266 * / (10^66)) (10^50) (3175614236544633 * / (10^16)).
Proof.
  unfold problem_45_spec.
  simpl.
  lra.
Qed.