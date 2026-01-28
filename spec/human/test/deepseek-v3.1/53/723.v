Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg1_neg2 : 
  problem_53_pre (-10)%Z (-999999999999999999999)%Z -> 
  problem_53_spec (-10)%Z (-999999999999999999999)%Z (-1000000000000000000009)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.