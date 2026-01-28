Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 20 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (H_split: k < 2 \/ k >= 2) by lia.
    destruct H_split as [H_small | H_large].
    + assert (H_vals: k = 0 \/ k = 1) by lia.
      destruct H_vals as [Hk0 | Hk1]; subst; simpl in Hk_eq; discriminate.
    + assert (H_pow: 5 ^ 2 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow.
      rewrite Hk_eq in H_pow.
      lia.
Qed.