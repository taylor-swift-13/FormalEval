Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for `add` *)
Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_case_problem_53 : problem_53_spec 999999 123456789098765432101234567891 123456789098765432101235567890.
Proof.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.