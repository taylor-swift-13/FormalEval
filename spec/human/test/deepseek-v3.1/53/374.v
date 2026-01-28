Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large_nums : 
  problem_53_pre 123456789098765432101234567892 123456789098765432101234567891 -> 
  problem_53_spec 123456789098765432101234567892 123456789098765432101234567891 246913578197530864202469135783.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.