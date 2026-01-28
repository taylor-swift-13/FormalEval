Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg2_large : 
  problem_53_pre (-2) 98765432101234567890123456790 -> 
  problem_53_spec (-2) 98765432101234567890123456790 98765432101234567890123456788.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.