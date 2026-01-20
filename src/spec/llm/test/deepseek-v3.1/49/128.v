Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 1000002%Z 1000000%Z 437504%Z.
Proof.
  unfold modp_spec.
  intro H.
  vm_compute.
  reflexivity.
Qed.