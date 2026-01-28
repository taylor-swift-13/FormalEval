Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 100019 172872 145184.
Proof.
  unfold modp_spec.
  vm_compute.
  reflexivity.
Qed.