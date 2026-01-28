Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg16_neg249 : problem_53_spec (-16) (-249) (-265).
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.