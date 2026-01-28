Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_530123_530123 : modp_spec 530123 530123 146627.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute.
    reflexivity.
Qed.