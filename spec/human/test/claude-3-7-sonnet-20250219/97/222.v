Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_minus12346_minus12346 :
  problem_97_spec (-12346) (-12346) 36.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.