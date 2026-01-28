Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example test_modp : modp_spec 9874 9875 7159.
Proof.
  unfold modp_spec.
  intros H.
  vm_compute.
  reflexivity.
Qed.