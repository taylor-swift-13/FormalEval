Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 6 81 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k = 0 \/ k > 0) as [Hk0 | Hk_pos] by lia.
    + subst k.
      simpl in Hk_eq.
      discriminate.
    + assert (Hk1 : 1 <= k) by lia.
      assert (Hpow : 81 ^ 1 <= 81 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk_eq in Hpow.
      simpl in Hpow.
      lia.
Qed.