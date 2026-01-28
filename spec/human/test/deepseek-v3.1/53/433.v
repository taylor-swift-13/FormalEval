Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg_large_and_small : 
  problem_53_pre (-123456789098765432101234567891) 10003 -> 
  problem_53_spec (-123456789098765432101234567891) 10003 (-123456789098765432101234557888).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.