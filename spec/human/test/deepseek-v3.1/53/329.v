Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg98_large : 
  problem_53_pre (-98)%Z 123456789098765432101234567891%Z -> 
  problem_53_spec (-98)%Z 123456789098765432101234567891%Z 123456789098765432101234567793%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.