Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg_9997_neg_1000000 : 
  problem_53_pre (-9997)%Z (-1000000)%Z -> 
  problem_53_spec (-9997)%Z (-1000000)%Z (-1009997)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.