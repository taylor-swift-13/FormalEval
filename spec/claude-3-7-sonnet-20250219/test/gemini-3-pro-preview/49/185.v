Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_999984_999985 : modp_spec 999984 999985 469736.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute.
    reflexivity.
Qed.