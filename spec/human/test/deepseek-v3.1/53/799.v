Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_6_neg123456789098765432101234567891 : 
  problem_53_pre 6 (-123456789098765432101234567891) -> 
  problem_53_spec 6 (-123456789098765432101234567891) (-123456789098765432101234567885).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.