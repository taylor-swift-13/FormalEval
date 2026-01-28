Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 7 15 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (Hk: k = 0 \/ k > 0) by lia.
    destruct Hk as [Hk0 | Hk_pos].
    + subst k. simpl in Hk_eq. discriminate.
    + assert (H_lower_bound: 15 <= 15 ^ k).
      {
        replace 15 with (15 ^ 1) by reflexivity.
        apply Z.pow_le_mono_r; lia.
      }
      rewrite Hk_eq in H_lower_bound.
      lia.
Qed.