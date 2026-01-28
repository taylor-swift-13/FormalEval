Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg9_large : 
  problem_53_pre (-9) 1000000000000000000 -> 
  problem_53_spec (-9) 1000000000000000000 999999999999999991.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.