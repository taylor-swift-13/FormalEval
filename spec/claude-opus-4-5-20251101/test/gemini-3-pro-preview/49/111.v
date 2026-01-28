Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.
Require Import Zpow_facts.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_100000_7: modp_spec 100000 7 2.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - replace 100000 with (3 * 33333 + 1) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_mul_r by lia.
    rewrite Z.mul_mod by lia.
    rewrite Zpower_mod by lia.
    replace (2 ^ 3 mod 7) with 1 by reflexivity.
    replace (1 ^ 33333) with 1 by reflexivity.
    reflexivity.
Qed.