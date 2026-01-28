Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_20_103: modp_spec 20 103 36.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 103 > 0 *)
    lia.
  - (* Prove 36 = (2 ^ 20) mod 103 *)
    reflexivity.
Qed.