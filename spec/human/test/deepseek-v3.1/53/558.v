Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_123456789098765432101234567893_neg97 : 
  problem_53_pre 123456789098765432101234567893 (-97) -> 
  problem_53_spec 123456789098765432101234567893 (-97) 123456789098765432101234567796.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.