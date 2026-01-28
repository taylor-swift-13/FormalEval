Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_12_7 : modp_spec 12 7 1.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.