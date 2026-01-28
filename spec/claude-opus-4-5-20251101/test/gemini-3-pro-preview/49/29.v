Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_23_200: modp_spec 23 200 8.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 200 > 0 *)
    lia.
  - (* Prove 8 = (2 ^ 23) mod 200 *)
    reflexivity.
Qed.