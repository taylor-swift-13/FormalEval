Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_9_1000001: modp_spec 9 1000001 512.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 1000001 > 0 *)
    lia.
  - (* Prove 512 = (2 ^ 9) mod 1000001 *)
    reflexivity.
Qed.