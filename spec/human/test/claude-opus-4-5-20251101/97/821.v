Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_246813578_neg8 : problem_97_spec 246813578 (-8) 64.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.