Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_233_101 : modp_spec 233 101 35.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.