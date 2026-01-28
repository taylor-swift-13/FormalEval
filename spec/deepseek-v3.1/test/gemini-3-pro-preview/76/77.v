Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 11 10 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Hpow]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst k. simpl in Hpow. discriminate.
    + subst k. simpl in Hpow. discriminate.
    + assert (10 ^ 2 <= 10 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H. rewrite Hpow in H. lia.
Qed.