Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 10 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_pow]].
    assert (H_cases: k < 4 \/ k >= 4) by lia.
    destruct H_cases as [H_small | H_large].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H as [ | [ | [ | ]]]; subst k; simpl in Hk_pow; discriminate.
    + assert (H_mono: 2 ^ 4 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite Hk_pow in H_mono.
      lia.
Qed.