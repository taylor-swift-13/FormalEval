Require Import Reals.
Require Import Psatz.  (* for lra *)
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec (side high output : R) : Prop :=
  output = side * high / 2.

Example problem_45_test_case :
  problem_45_pre 5 3 /\ problem_45_spec 5 3 7.5.
Proof.
  split.
  - (* precondition *)
    unfold problem_45_pre.
    split; lra.
  - (* specification *)
    unfold problem_45_spec.
    (* 7.5 = 5 * 3 / 2 *)
    rewrite <- Rmult_assoc.
    field_simplify.
    ring.
Qed.