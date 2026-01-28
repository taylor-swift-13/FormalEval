Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 999999 18 8.
Proof.
  unfold modp_spec.
  vm_compute.
  reflexivity.
Qed.