Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_7_9877: modp_spec 7 9877 128.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 9877 > 0 *)
    lia.
  - (* Prove 128 = (2 ^ 7) mod 9877 *)
    reflexivity.
Qed.