Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_19_18 : modp_spec 19 18 2.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.