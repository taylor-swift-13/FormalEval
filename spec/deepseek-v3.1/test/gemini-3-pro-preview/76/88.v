Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 37 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Hpow]].
    assert (k = 0 \/ k = 1 \/ k = 2 \/ k >= 3) as [Hk | [Hk | [Hk | Hk]]] by lia.
    + subst k. simpl in Hpow. discriminate.
    + subst k. simpl in Hpow. discriminate.
    + subst k. simpl in Hpow. discriminate.
    + assert (6 ^ 3 <= 6 ^ k) by (apply Z.pow_le_mono_r; lia).
      rewrite Hpow in H.
      simpl in H.
      lia.
Qed.