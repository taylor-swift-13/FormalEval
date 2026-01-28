Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_5_5: modp_spec 5 5 2.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 5 > 0 *)
    lia.
  - (* Prove 2 = (2 ^ 5) mod 5 *)
    reflexivity.
Qed.