Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_78_100 : modp_spec 78 100 44.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.