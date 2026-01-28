Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 16777216 16777217 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    destruct (Z.eq_dec k 0) as [Hk0 | Hk_pos].
    + subst k. simpl in Hk2. lia.
    + assert (1 <= k) by lia.
      assert (16777217 ^ 1 <= 16777217 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hle.
      rewrite Hk2 in Hle.
      lia.
Qed.