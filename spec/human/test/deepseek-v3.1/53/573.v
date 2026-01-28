Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large_numbers : 
  problem_53_pre 999996 1000000000000000000000 -> 
  problem_53_spec 999996 1000000000000000000000 1000000000000000999996.
Proof.
  intros _.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.