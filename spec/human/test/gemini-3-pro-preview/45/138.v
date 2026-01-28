Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [6.351228473089266e-51; 1000000000000], output = 3.175614236544633e-39 *)
Example problem_45_test : problem_45_spec (6351228473089266 * / 10^66) (10^12) (3175614236544633 * / 10^54).
Proof.
  unfold problem_45_spec.
  replace (10^66) with (10^54 * 10^12) by (replace 66%nat with (54 + 12)%nat by reflexivity; rewrite pow_add; reflexivity).
  field; repeat (try apply pow_nonzero; try lra).
Qed.