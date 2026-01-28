Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 64 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk Hpow]].
    assert (k < 3 \/ k >= 3) as [Hsmall | Hlarge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2) as [E | [E | E]] by lia;
      rewrite E in Hpow; simpl in Hpow; lia.
    + assert (Hmono : 6 ^ 3 <= 6 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hpow in Hmono.
      simpl in Hmono.
      lia.
Qed.