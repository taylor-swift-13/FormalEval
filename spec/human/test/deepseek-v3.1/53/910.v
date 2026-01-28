Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg999997_9999 : 
  problem_53_pre (-999997) 9999 -> 
  problem_53_spec (-999997) 9999 (-989998).
Proof.
  intros _.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.