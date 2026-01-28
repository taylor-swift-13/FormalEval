Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_999999999999999999998_98765432101234567890123456788 : 
  problem_53_pre 999999999999999999998 98765432101234567890123456788 -> 
  problem_53_spec 999999999999999999998 98765432101234567890123456788 98765433101234567890123456786.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.