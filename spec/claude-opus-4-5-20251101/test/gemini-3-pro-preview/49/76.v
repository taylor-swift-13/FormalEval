Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_19_50: modp_spec 19 50 38.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 50 > 0 *)
    lia.
  - (* Prove 38 = (2 ^ 19) mod 50 *)
    reflexivity.
Qed.