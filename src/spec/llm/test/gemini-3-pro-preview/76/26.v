Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 6 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Hx]].
    assert (Hcases: k < 2 \/ k >= 2) by lia.
    destruct Hcases as [Hlt | Hge].
    + assert (Hsmall: k = 0 \/ k = 1) by lia.
      destruct Hsmall as [H0 | H1]; subst k; simpl in Hx; discriminate Hx.
    + assert (Hpow: 5 ^ 2 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      rewrite <- Hx in Hpow.
      lia.
Qed.