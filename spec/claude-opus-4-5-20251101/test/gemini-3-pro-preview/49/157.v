Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_1000002_1000002: modp_spec 1000002 1000002 64.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 1000002 > 0 *)
    lia.
  - (* Prove 64 = (2 ^ 1000002) mod 1000002 *)
    vm_compute.
    reflexivity.
Qed.