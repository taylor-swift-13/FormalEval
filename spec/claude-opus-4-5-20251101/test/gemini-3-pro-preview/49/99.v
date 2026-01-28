Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_21_103: modp_spec 21 103 72.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.