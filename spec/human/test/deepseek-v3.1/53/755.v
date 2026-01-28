Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_0_1 : 
  problem_53_pre (-999999999999999999999) (-1000000000000000000001) -> 
  problem_53_spec (-999999999999999999999) (-1000000000000000000001) (-2000000000000000000000).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.