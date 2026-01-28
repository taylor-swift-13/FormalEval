Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_36_7: modp_spec 36 7 1.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 7 > 0 *)
    lia.
  - (* Prove 1 = (2 ^ 36) mod 7 *)
    reflexivity.
Qed.