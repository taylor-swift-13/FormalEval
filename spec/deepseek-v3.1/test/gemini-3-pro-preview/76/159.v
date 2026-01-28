Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 2 81 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_pow]].
    assert (k = 0 \/ k >= 1) as [Hk0 | Hk1] by lia.
    + subst k. simpl in Hk_pow. discriminate.
    + assert (81 ^ 1 <= 81 ^ k) as H_mono.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite Hk_pow in H_mono.
      lia.
Qed.