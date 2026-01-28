Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_37_80 : modp_spec 37 80 32.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.