Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example greatest_common_divisor_spec_968_968 :
  greatest_common_divisor_spec 968%Z 968%Z 968%Z.
Proof.
  unfold greatest_common_divisor_spec.
  vm_compute.
  reflexivity.
Qed.