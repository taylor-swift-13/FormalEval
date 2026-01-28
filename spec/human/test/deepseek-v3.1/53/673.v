Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg8_neg9999 : 
  problem_53_pre (-8)%Z (-9999)%Z -> 
  problem_53_spec (-8)%Z (-9999)%Z (-10007)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.