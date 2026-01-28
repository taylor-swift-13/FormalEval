Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 8 9877 256.
Proof.
  unfold modp_spec.
  reflexivity.
Qed.