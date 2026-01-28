Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg100_neg101 : problem_53_spec (-100) (-101) (-201).
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.