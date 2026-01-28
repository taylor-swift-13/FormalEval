Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_10_10: modp_spec 10 10 4.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 10 > 0 *)
    lia.
  - (* Prove 4 = (2 ^ 10) mod 10 *)
    reflexivity.
Qed.