Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 35 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k < 3 \/ k >= 3) as [Hlt | Hge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2) as [K0 | [K1 | K2]] by lia.
      * subst k; simpl in Heq; discriminate.
      * subst k; simpl in Heq; discriminate.
      * subst k; simpl in Heq; discriminate.
    + assert (Hpow: 5 ^ 3 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      lia.
Qed.