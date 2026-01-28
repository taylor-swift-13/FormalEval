Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 64 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    inversion H.
  - intros [k [Hk_ge Hk_eq]].
    assert (k < 3 \/ k >= 3) by lia.
    destruct H as [H_small | H_large].
    + assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [H0 | [H1 | H2]]; subst k; simpl in Hk_eq; discriminate.
    + assert (5 ^ 3 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite Hk_eq in H.
      lia.
Qed.