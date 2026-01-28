Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2187 1099511627776 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (H_cases: k = 0 \/ 1 <= k) by lia.
    destruct H_cases as [H0 | H1].
    + subst k. simpl in Heq. discriminate.
    + assert (H_pow: 1099511627776 ^ 1 <= 1099511627776 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Z.pow_1_r in H_pow.
      rewrite <- Heq in H_pow.
      lia.
Qed.