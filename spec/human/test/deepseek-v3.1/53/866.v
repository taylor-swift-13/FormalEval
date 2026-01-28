Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg_large_five : 
  problem_53_pre (-98765432101234567890123456791)%Z 5%Z -> 
  problem_53_spec (-98765432101234567890123456791)%Z 5%Z (-98765432101234567890123456786)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.