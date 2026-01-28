Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 27 246 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Hpow]].
    destruct (Z.eq_dec k 0) as [Hk0 | Hk_neq_0].
    + subst k. simpl in Hpow. discriminate.
    + assert (Hk_pos: 0 < k) by lia.
      assert (Hineq: 246 ^ 1 <= 246 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hineq.
      rewrite Hpow in Hineq.
      lia.
Qed.