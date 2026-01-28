Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for `add` *)
Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_case_problem_53 : problem_53_spec 123456789098765432101234567891%Z 98765432101234567890123456786%Z 222222221199999999991358024677%Z.
Proof.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.