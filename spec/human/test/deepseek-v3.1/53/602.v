Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg999999_1_0000000000000000000000 : 
  problem_53_pre (-999999)%Z 1000000000000000000000%Z -> 
  problem_53_spec (-999999)%Z 1000000000000000000000%Z 999999999999999000001%Z.
Proof.
  intros Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.