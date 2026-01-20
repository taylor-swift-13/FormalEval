Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example greatest_common_divisor_spec_234567888_3699638 :
  greatest_common_divisor_spec 234567888%Z 3699638%Z 2%Z.
Proof.
  unfold greatest_common_divisor_spec.
  vm_compute.
  reflexivity.
Qed.