Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_101_200: modp_spec 101 200 152.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 200 > 0 *)
    lia.
  - (* Prove 152 = (2 ^ 101) mod 200 *)
    vm_compute. reflexivity.
Qed.