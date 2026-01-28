Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_minus_999999_minus_11 : 
  problem_53_pre (-999999)%Z (-11)%Z -> 
  problem_53_spec (-999999)%Z (-11)%Z (-1000010)%Z.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.