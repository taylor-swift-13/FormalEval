Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_8_78: modp_spec 8 78 22.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 78 > 0 *)
    lia.
  - (* Prove 22 = (2 ^ 8) mod 78 *)
    reflexivity.
Qed.