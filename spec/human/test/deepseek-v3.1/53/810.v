Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg_large : 
  problem_53_pre (-999999999999999999998)%Z (-999999999999999999999)%Z -> 
  problem_53_spec (-999999999999999999998)%Z (-999999999999999999999)%Z (-1999999999999999999997)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.