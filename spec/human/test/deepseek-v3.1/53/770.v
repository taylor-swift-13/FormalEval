Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg999997_neg98 : 
  problem_53_pre (-999997)%Z (-98)%Z -> 
  problem_53_spec (-999997)%Z (-98)%Z (-1000095)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.