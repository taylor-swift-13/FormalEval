Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_112_112: modp_spec 112 112 16.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 112 > 0 *)
    lia.
  - (* Prove 16 = (2 ^ 112) mod 112 *)
    reflexivity.
Qed.