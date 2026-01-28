Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg10000_neg99 : problem_53_spec (-10000) (-99) (-10099).
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.