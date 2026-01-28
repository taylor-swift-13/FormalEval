Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_10_17: modp_spec 10 17 4.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.