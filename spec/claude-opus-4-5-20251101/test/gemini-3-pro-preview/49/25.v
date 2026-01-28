Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_17_20: modp_spec 17 20 12.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 20 > 0 *)
    lia.
  - (* Prove 12 = (2 ^ 17) mod 20 *)
    reflexivity.
Qed.