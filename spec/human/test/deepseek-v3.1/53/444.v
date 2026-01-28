Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_big_numbers : 
  problem_53_pre (-123456789098765432101234567891%Z) (98765432101234567890123456790%Z) -> 
  problem_53_spec (-123456789098765432101234567891%Z) (98765432101234567890123456790%Z) (-24691356997530864211111111101%Z).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  reflexivity.
Qed.