Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [1e+50; 1e+50], output = 5e+99 *)
Example problem_45_test : problem_45_spec (10^50) (10^50) (5 * 10^99).
Proof.
  unfold problem_45_spec.
  replace (5 * 10^99) with (10 * 10^99 / 2) by lra.
  replace (10 * 10^99) with (10^1 * 10^99) by (simpl; ring).
  rewrite <- (pow_add 10 50 50).
  rewrite <- (pow_add 10 1 99).
  replace (50 + 50)%nat with 100%nat by reflexivity.
  replace (1 + 99)%nat with 100%nat by reflexivity.
  field.
Qed.