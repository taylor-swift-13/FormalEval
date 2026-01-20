Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example greatest_common_divisor_spec_100000000_123456788 :
  greatest_common_divisor_spec 100000000%Z 123456788%Z 4%Z.
Proof.
  unfold greatest_common_divisor_spec.
  vm_compute.
  reflexivity.
Qed.