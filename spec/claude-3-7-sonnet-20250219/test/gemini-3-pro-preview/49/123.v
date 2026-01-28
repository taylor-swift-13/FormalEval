Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_172871_172871 : modp_spec 172871 172871 2.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute.
    reflexivity.
Qed.