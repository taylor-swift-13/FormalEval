Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 82 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hge Hpow]].
    assert (H_cases: k < 7 \/ k >= 7) by lia.
    destruct H_cases as [Hlt | Hge7].
    + assert (Hle6: k <= 6) by lia.
      assert (H_pow_le: 2 ^ k <= 2 ^ 6).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hpow in H_pow_le.
      simpl in H_pow_le.
      lia.
    + assert (H_pow_le: 2 ^ 7 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hpow in H_pow_le.
      simpl in H_pow_le.
      lia.
Qed.