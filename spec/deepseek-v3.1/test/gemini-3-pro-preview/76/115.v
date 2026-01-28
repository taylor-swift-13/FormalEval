Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 2188 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (k < 7 \/ k = 7 \/ 7 < k) as [Hlt | [Heq | Hgt]] by lia.
    + assert (3 ^ k < 3 ^ 7) by (apply Z.pow_lt_mono_r; lia).
      rewrite Hk2 in H.
      simpl in H.
      lia.
    + subst k.
      simpl in Hk2.
      lia.
    + assert (3 ^ 8 <= 3 ^ k) by (apply Z.pow_le_mono_r; lia).
      rewrite Hk2 in H.
      simpl in H.
      lia.
Qed.