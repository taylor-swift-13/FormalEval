Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_6_20: modp_spec 6 20 4.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 20 > 0 *)
    lia.
  - (* Prove 4 = (2 ^ 6) mod 20 *)
    reflexivity.
Qed.