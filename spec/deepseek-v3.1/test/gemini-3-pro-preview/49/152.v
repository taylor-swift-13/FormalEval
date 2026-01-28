Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example test_modp : modp_spec 100019 172872 145184.
Proof.
  unfold modp_spec.
  intros H.
  vm_compute.
  reflexivity.
Qed.