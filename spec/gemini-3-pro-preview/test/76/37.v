Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 10 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k < 3 \/ k >= 3) as [Hlt | Hge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2) as [ | [ | ]] by lia;
      subst k; simpl in Hk2; discriminate.
    + assert (3 ^ 3 <= 3 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in Hpow.
      change (3 ^ 3) with 27 in Hpow.
      lia.
Qed.