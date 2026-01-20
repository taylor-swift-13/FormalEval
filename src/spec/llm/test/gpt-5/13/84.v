Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example greatest_common_divisor_spec_10_11 :
  greatest_common_divisor_spec 10%Z 11%Z 1%Z.
Proof.
  unfold greatest_common_divisor_spec.
  vm_compute.
  reflexivity.
Qed.