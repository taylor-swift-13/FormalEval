Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_200_8: modp_spec 200 8 0.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 8 > 0 *)
    lia.
  - (* Prove 0 = (2 ^ 200) mod 8 *)
    reflexivity.
Qed.