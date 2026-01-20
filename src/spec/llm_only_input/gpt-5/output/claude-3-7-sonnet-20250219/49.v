Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example modp_spec_example : modp_spec 3%Z 5%Z 3%Z.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute. reflexivity.
Qed.