Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large_numbers : 
  problem_53_pre 123456789098765432101234567891 98765432101234567890123456789 -> 
  problem_53_spec 123456789098765432101234567891 98765432101234567890123456789 222222221199999999991358024680.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  reflexivity.
Qed.