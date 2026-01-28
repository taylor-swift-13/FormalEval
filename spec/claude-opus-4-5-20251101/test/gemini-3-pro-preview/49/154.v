Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_16_16: modp_spec 16 16 0.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 16 > 0 *)
    lia.
  - (* Prove 0 = (2 ^ 16) mod 16 *)
    reflexivity.
Qed.