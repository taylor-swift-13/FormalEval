Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example modp_spec_test : modp_spec 3%Z 5%Z 3%Z.
Proof.
  unfold modp_spec.
  vm_compute.
  reflexivity.
Qed.