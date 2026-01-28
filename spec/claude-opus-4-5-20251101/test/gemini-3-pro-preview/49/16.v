Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_50_23: modp_spec 50 23 18.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.