Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large_numbers : 
  problem_53_pre 98765432101234567890123456789 98765432101234567890123456790 -> 
  problem_53_spec 98765432101234567890123456789 98765432101234567890123456790 197530864202469135780246913579.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.