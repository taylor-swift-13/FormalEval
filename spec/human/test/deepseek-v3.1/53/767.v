Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg100_999999999999999999998 : 
  problem_53_pre (-100)%Z 999999999999999999998%Z -> 
  problem_53_spec (-100)%Z 999999999999999999998%Z 999999999999999999898%Z.
Proof.
  intros Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.