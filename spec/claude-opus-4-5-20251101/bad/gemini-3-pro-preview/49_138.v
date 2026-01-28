Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_54321_54321: modp_spec 54321 54321 33053.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - rewrite <- Z.pow_mod_def by lia.
    vm_compute.
    reflexivity.
Qed.