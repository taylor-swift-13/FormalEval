Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_66_98765432101234567890123456790 : 
  problem_53_pre 66 98765432101234567890123456790 -> 
  problem_53_spec 66 98765432101234567890123456790 98765432101234567890123456856.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.