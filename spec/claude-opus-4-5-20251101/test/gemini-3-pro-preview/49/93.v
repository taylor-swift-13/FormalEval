Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_100_18: modp_spec 100 18 16.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.