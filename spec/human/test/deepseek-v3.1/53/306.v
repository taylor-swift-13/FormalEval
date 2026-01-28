Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg1_neg2 : 
  problem_53_pre (-9999%Z) (-10001%Z) -> 
  problem_53_spec (-9999%Z) (-10001%Z) (-20000%Z).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.