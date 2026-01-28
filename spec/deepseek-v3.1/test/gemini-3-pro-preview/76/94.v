Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 10 11 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Hpow]].
    destruct (Z.eq_dec k 0) as [Heq | Hneq].
    + subst k. simpl in Hpow. discriminate Hpow.
    + assert (1 <= k) by lia.
      assert (11 ^ 1 <= 11 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hpow in H0.
      simpl in H0.
      lia.
Qed.