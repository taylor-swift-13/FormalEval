Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_large_numbers : 
  problem_53_pre 9998 98765432101234567890123456787 -> 
  problem_53_spec 9998 98765432101234567890123456787 98765432101234567890123466785.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.