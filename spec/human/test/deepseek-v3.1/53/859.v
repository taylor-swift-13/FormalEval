Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg999998_99 : 
  problem_53_pre (-999998) 99 -> 
  problem_53_spec (-999998) 99 (-999899).
Proof.
  intros Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.