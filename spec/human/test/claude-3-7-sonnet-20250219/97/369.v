Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg12344_6787 :
  problem_97_spec (-12344) 6787 28.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.