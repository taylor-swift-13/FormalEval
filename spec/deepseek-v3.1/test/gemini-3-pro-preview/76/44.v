Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 81 7 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k < 3 \/ k >= 3) by lia.
    destruct H as [H_small | H_large].
    + assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [H0 | [H1 | H2]]; subst k; simpl in Hk_eq; discriminate.
    + assert (7 ^ 3 <= 7 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk_eq in H.
      simpl in H.
      lia.
Qed.