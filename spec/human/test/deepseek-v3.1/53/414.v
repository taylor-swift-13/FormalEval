Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg_large_zero : 
  problem_53_pre (-1000000000000000000000)%Z 0%Z -> 
  problem_53_spec (-1000000000000000000000)%Z 0%Z (-1000000000000000000000)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.