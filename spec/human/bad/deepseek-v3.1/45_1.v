Require Import Reals.
Require Import ZArith.
Open Scope R_scope.

Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
  output = side * high / 2.

Example triangle_area_example : problem_45_spec 5 3 7.5.
Proof.
  unfold problem_45_spec.
  compute.
  reflexivity.
Qed.