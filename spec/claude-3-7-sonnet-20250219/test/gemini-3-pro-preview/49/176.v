Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_1048576_524 : modp_spec 1048576 524 172.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute.
    reflexivity.
Qed.