Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 7 9877 128.
Proof.
  unfold modp_spec.
  reflexivity.
Qed.