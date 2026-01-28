Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_21_102: modp_spec 21 102 32.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 102 > 0 *)
    lia.
  - (* Prove 32 = (2 ^ 21) mod 102 *)
    reflexivity.
Qed.