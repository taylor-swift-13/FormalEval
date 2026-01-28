Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_50_17: modp_spec 50 17 4.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 17 > 0 *)
    lia.
  - (* Prove 4 = (2 ^ 50) mod 17 *)
    reflexivity.
Qed.