Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_some_large_input : 
  problem_53_pre 98765432101234567890123456790 123456789098765432101234567892 -> 
  problem_53_spec 98765432101234567890123456790 123456789098765432101234567892 222222221199999999991358024682.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.