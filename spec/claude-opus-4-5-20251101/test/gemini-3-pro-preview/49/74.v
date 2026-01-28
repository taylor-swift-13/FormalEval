Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_19_200: modp_spec 19 200 88.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 200 > 0 *)
    lia.
  - (* Prove 88 = (2 ^ 19) mod 200 *)
    reflexivity.
Qed.