Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_5_17: modp_spec 5 17 15.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 17 > 0 *)
    lia.
  - (* Prove 15 = (2 ^ 5) mod 17 *)
    reflexivity.
Qed.