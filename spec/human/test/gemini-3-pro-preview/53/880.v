Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_case_problem_53 : problem_53_spec 1000000000000000000000%Z 1000001%Z 1000000000000001000001%Z.
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.