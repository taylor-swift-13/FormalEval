Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

Example problem_45_test : 
  Rabs (109.05678076166014%R - 14.768668237973262%R * 14.768668237973262%R / 2) < 1e-10.
Proof.
  unfold Rabs.
  case Rcase_abs; lra.
Qed.