Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_172869_172869: modp_spec 172869 172869 21761.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 172869 > 0 *)
    lia.
  - (* Prove 21761 = (2 ^ 172869) mod 172869 *)
    vm_compute.
    reflexivity.
Qed.