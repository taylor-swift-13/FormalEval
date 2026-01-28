Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_100_3: modp_spec 100 3 1.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 3 > 0 *)
    lia.
  - (* Prove 1 = (2 ^ 100) mod 3 *)
    reflexivity.
Qed.