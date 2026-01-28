Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_neg_large : 
  problem_53_pre (-9)%Z (-123456789098765432101234567890)%Z -> 
  problem_53_spec (-9)%Z (-123456789098765432101234567890)%Z (-123456789098765432101234567899)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.