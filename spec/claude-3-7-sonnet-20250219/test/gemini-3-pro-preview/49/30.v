Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_78_79 : modp_spec 78 79 1.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.