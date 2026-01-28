Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg_large_and_pos : 
  problem_53_pre (-98765432101234567890123456790) 1000001 -> 
  problem_53_spec (-98765432101234567890123456790) 1000001 (-98765432101234567890122456789).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.