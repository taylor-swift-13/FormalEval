Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_67_and_large : 
  problem_53_pre 67 98765432101234567890123456789 -> 
  problem_53_spec 67 98765432101234567890123456789 98765432101234567890123456856.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.