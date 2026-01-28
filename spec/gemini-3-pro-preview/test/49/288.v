Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 172870 1048577 1047553.
Proof.
  unfold modp_spec.
  vm_compute.
  reflexivity.
Qed.