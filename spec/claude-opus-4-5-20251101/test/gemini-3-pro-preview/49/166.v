Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_233_172871: modp_spec 233 172871 12294.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 172871 > 0 *)
    lia.
  - (* Prove 12294 = (2 ^ 233) mod 172871 *)
    vm_compute.
    reflexivity.
Qed.