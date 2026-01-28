Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_case_problem_53 : problem_53_spec 98765432101234567890123456791%Z (-1)%Z 98765432101234567890123456790%Z.
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.