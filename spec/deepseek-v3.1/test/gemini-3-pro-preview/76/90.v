Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 65 64 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (H_cases: k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H_cases as [H0 | [H1 | H2]].
    + subst k. simpl in Hk2. lia.
    + subst k. simpl in Hk2. lia.
    + assert (H_mono: 64 ^ 2 <= 64 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite Hk2 in H_mono.
      lia.
Qed.