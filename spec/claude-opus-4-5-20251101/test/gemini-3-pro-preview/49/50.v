Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_99_20: modp_spec 99 20 8.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 20 > 0 *)
    lia.
  - (* Prove 8 = (2 ^ 99) mod 20 *)
    vm_compute.
    reflexivity.
Qed.