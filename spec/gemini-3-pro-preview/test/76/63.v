Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 125 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (H_cases: k < 3 \/ k >= 3) by lia.
    destruct H_cases as [H_small | H_large].
    + assert (k = 0 \/ k = 1 \/ k = 2) as H_vals by lia.
      destruct H_vals as [E | [E | E]]; subst; simpl in Hk_eq; discriminate.
    + assert (H_mono: 6 ^ 3 <= 6 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite <- Hk_eq in H_mono.
      lia.
Qed.