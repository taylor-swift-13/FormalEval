Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_9876_9876: modp_spec 9876 9876 4096.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 9876 > 0 *)
    lia.
  - (* Prove 4096 = (2 ^ 9876) mod 9876 *)
    vm_compute.
    reflexivity.
Qed.