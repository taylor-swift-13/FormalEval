Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [0.09250267285921429; 1000], output = 46.251336429607145 *)
Example problem_45_test : problem_45_spec 0.09250267285921429 1000 46.251336429607145.
Proof.
  unfold problem_45_spec.
  lra.
Qed.