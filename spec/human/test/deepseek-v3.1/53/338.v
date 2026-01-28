Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_example_1 : 
  problem_53_pre 10002 123456789098765432101234567889 -> 
  problem_53_spec 10002 123456789098765432101234567889 123456789098765432101234577891.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.