Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_5_98765432101234567890123456787 : 
  problem_53_pre 5 98765432101234567890123456787 -> 
  problem_53_spec 5 98765432101234567890123456787 98765432101234567890123456792.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.