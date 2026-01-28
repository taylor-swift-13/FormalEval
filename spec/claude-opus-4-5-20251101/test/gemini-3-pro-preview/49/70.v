Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_20_19: modp_spec 20 19 4.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 19 > 0 *)
    lia.
  - (* Prove 4 = (2 ^ 20) mod 19 *)
    reflexivity.
Qed.