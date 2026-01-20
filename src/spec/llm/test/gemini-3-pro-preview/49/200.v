Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 235 1009 278.
Proof.
  unfold modp_spec.
  reflexivity.
Qed.