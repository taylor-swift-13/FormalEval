Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example problem_97_test_1 :
  problem_97_spec 124%Z 100%Z 0%Z.
Proof.
  unfold problem_97_spec.
  vm_compute.
  reflexivity.
Qed.