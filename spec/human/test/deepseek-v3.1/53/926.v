Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg8_1_000000000000000000000 : 
  problem_53_pre (-8) 1000000000000000000000 -> 
  problem_53_spec (-8) 1000000000000000000000 999999999999999999992.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.