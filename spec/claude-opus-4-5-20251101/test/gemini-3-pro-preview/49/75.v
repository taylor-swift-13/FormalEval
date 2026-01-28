Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_98_4: modp_spec 98 4 0.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 4 > 0 *)
    lia.
  - (* Prove 0 = (2 ^ 98) mod 4 *)
    vm_compute.
    reflexivity.
Qed.