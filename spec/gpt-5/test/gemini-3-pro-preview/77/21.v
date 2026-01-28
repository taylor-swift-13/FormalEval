Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_2 : iscube_spec (-63) false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. inversion H.
  - intros [k Hk].
    assert (H_cases: k <= -4 \/ k = -3 \/ k = -2 \/ k = -1 \/ k = 0 \/ k >= 1) by lia.
    destruct H_cases as [H | [H | [H | [H | [H | H]]]]].
    + assert (H_pow: k ^ 3 <= (-4) ^ 3).
      { apply Z.pow_le_mono_l; lia. }
      rewrite Hk in H_pow.
      simpl in H_pow.
      lia.
    + subst. simpl in Hk. lia.
    + subst. simpl in Hk. lia.
    + subst. simpl in Hk. lia.
    + subst. simpl in Hk. lia.
    + assert (H_pow: 1 ^ 3 <= k ^ 3).
      { apply Z.pow_le_mono_l; lia. }
      rewrite Hk in H_pow.
      simpl in H_pow.
      lia.
Qed.