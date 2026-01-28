Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_case_2 : 
  problem_53_pre (-98765432101234567890123456790%Z) (-123456789098765432101234567890%Z) -> 
  problem_53_spec (-98765432101234567890123456790%Z) (-123456789098765432101234567890%Z) (-222222221199999999991358024680%Z).
Proof.
  intros _.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.