Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_17_21: modp_spec 17 21 11.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 21 > 0 *)
    lia.
  - (* Prove 11 = (2 ^ 17) mod 21 *)
    reflexivity.
Qed.