Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_17_100: modp_spec 17 100 72.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 100 > 0 *)
    lia.
  - (* Prove 72 = (2 ^ 17) mod 100 *)
    reflexivity.
Qed.