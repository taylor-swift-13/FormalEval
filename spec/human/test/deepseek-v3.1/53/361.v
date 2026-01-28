Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg999996_1_000000000000000000 : 
  problem_53_pre (-999996)%Z 1000000000000000000%Z -> 
  problem_53_spec (-999996)%Z 1000000000000000000%Z 999999999999000004%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.