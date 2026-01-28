Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_50_79: modp_spec 50 79 73.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 79 > 0 *)
    lia.
  - (* Prove 73 = (2 ^ 50) mod 79 *)
    reflexivity.
Qed.