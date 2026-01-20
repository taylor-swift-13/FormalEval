Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example greatest_common_divisor_spec_108_123456790 :
  greatest_common_divisor_spec 108%Z 123456790%Z 2%Z.
Proof.
  unfold greatest_common_divisor_spec.
  vm_compute.
  reflexivity.
Qed.