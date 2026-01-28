Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_neg_large_numbers : 
  problem_53_pre (-999999999999999999998%Z) (-123456789098765432101234567891%Z) -> 
  problem_53_spec (-999999999999999999998) (-123456789098765432101234567891) (-123456790098765432101234567889).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.