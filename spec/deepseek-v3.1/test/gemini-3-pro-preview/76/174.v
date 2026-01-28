Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 65537 245 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k < 3 \/ k >= 3) as [Hsmall | Hlarge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2) as [-> | [-> | ->]] by lia.
      * simpl in Hk2. lia.
      * simpl in Hk2. lia.
      * simpl in Hk2. lia.
    + assert (245 ^ 3 <= 245 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      rewrite Hk2 in Hpow.
      lia.
Qed.