Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large_numbers : 
  problem_53_pre 999999999999999999999 999999999999999999998 -> 
  problem_53_spec 999999999999999999999 999999999999999999998 1999999999999999999997.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.