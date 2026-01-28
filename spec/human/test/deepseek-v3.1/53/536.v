Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_1000001_98765432101234567890123456789 : 
  problem_53_pre 1000001 98765432101234567890123456789 -> 
  problem_53_spec 1000001 98765432101234567890123456789 98765432101234567890124456790.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.