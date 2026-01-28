Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg999999_and_large : 
  problem_53_pre (-999999)%Z  (98765432101234567890123456791)%Z -> 
  problem_53_spec (-999999)%Z  (98765432101234567890123456791)%Z  (98765432101234567890122456792)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.