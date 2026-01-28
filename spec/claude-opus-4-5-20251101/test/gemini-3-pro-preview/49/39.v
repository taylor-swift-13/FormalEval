Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_7_101: modp_spec 7 101 27.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 101 > 0 *)
    lia.
  - (* Prove 27 = (2 ^ 7) mod 101 *)
    reflexivity.
Qed.