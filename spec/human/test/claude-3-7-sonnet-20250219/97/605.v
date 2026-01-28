Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_246813579_neg123457 :
  problem_97_spec 246813579 (-123457) 63.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.