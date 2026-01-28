Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_sum_big_numbers : 
  problem_53_pre 10003 123456789098765432101234567889 -> 
  problem_53_spec 10003 123456789098765432101234567889 123456789098765432101234577892.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.