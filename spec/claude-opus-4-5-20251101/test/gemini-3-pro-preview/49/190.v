Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_9877_9876: modp_spec 9877 9876 8192.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 9876 > 0 *)
    lia.
  - (* Prove 8192 = (2 ^ 9877) mod 9876 *)
    vm_compute.
    reflexivity.
Qed.