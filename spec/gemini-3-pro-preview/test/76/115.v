Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2188 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Heq]].
    assert (Hcases: k < 7 \/ k = 7 \/ k > 7) by lia.
    destruct Hcases as [Hlt | [Heq7 | Hgt]].
    + assert (Hpow: 3 ^ k < 3 ^ 7) by (apply Z.pow_lt_mono_r; lia).
      replace (3 ^ 7) with 2187 in Hpow by reflexivity.
      lia.
    + subst k.
      replace (3 ^ 7) with 2187 in Heq by reflexivity.
      lia.
    + assert (Hpow: 3 ^ 8 <= 3 ^ k) by (apply Z.pow_le_mono_r; lia).
      replace (3 ^ 8) with 6561 in Hpow by reflexivity.
      lia.
Qed.