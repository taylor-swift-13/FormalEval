Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg6_neg5 : problem_53_spec (-6) (-5) (-11).
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.