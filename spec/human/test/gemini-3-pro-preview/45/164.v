Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

(* Test case: input = [5.933203128831868; 5.594645686633063], output = 16.5970846463185 *)
Example problem_45_test : problem_45_spec 5.933203128831868 5.594645686633063 (5.933203128831868 * 5.594645686633063 / 2).
Proof.
  unfold problem_45_spec.
  lra.
Qed.