Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 522 100000 14304.
Proof.
  unfold modp_spec.
  reflexivity.
Qed.