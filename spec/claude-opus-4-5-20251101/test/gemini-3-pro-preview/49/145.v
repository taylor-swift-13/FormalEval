Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_17_1009: modp_spec 17 1009 911.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 1009 > 0 *)
    lia.
  - (* Prove 911 = (2 ^ 17) mod 1009 *)
    reflexivity.
Qed.