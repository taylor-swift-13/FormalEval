Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg1000000_98765432101234567890123456791 : 
  problem_53_pre (-1000000) 98765432101234567890123456791 -> 
  problem_53_spec (-1000000) 98765432101234567890123456791 98765432101234567890122456791.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.