Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_minus123457_minus123457 : problem_97_spec (-123457) (-123457) 49.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.