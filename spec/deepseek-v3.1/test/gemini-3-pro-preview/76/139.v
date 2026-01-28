Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 245 2188 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Hpow]].
    destruct (Z.eq_dec k 0).
    + subst. simpl in Hpow. discriminate.
    + assert (k >= 1) by lia.
      assert (2188 ^ 1 <= 2188 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H0.
      rewrite Hpow in H0.
      lia.
Qed.