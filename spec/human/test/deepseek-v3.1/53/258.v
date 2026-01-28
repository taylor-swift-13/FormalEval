Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large_and_negative : 
  problem_53_pre 123456789098765432101234567890 (-999998) -> 
  problem_53_spec 123456789098765432101234567890 (-999998) 123456789098765432101233567892.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.