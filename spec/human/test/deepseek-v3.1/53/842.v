Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large_minus : 
  problem_53_pre 98765432101234567890123456789 (-999999) -> 
  problem_53_spec 98765432101234567890123456789 (-999999) 98765432101234567890122456790.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.