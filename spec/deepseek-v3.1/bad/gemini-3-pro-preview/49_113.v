Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example test_modp : modp_spec 1000000 999983 262144.
Proof.
  unfold modp_spec.
  intros H.
  rewrite <- Z.pow_mod_spec by (vm_compute; reflexivity).
  vm_compute.
  reflexivity.
Qed.