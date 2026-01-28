Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_172870_172870: modp_spec 172870 172870 61594.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 172870 > 0 *)
    lia.
  - (* Prove 61594 = (2 ^ 172870) mod 172870 *)
    vm_compute.
    reflexivity.
Qed.