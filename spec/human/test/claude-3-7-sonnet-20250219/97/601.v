Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2938475610_neg12345 :
  problem_97_spec 2938475610%Z (-12345)%Z 0%Z.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.