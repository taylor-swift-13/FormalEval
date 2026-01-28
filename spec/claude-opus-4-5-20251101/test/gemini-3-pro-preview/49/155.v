Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_7_233: modp_spec 7 233 128.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 233 > 0 *)
    lia.
  - (* Prove 128 = (2 ^ 7) mod 233 *)
    reflexivity.
Qed.