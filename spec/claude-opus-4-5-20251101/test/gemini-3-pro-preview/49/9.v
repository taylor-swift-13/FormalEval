Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_10_23: modp_spec 10 23 12.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 23 > 0 *)
    lia.
  - (* Prove 12 = (2 ^ 10) mod 23 *)
    reflexivity.
Qed.