Require Import Reals.
Require Import ZArith.
Open Scope R_scope.
Open Scope Z_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec (side high output : R) : Prop :=
  output = side * high / 2.

Example problem_45_test_case_1 : 
  problem_45_spec 5 3 7.5.
Proof.
  unfold problem_45_spec.
  simpl.
  field.
Qed.