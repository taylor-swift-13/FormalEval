Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_7_78: modp_spec 7 78 50.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 78 > 0 *)
    lia.
  - (* Prove 50 = (2 ^ 7) mod 78 *)
    reflexivity.
Qed.