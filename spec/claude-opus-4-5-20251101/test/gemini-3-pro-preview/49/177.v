Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_51_50: modp_spec 51 50 48.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 50 > 0 *)
    lia.
  - (* Prove 48 = (2 ^ 51) mod 50 *)
    reflexivity.
Qed.