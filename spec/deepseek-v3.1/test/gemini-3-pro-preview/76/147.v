Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 2188 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (H_cases: k < 11 \/ k = 11 \/ k > 11) by lia.
    destruct H_cases as [H_lt | [H_eq | H_gt]].
    + assert (2 ^ k <= 2 ^ 10) as H_pow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow.
      lia.
    + subst k.
      simpl in Hk_eq.
      discriminate.
    + assert (2 ^ 12 <= 2 ^ k) as H_pow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow.
      lia.
Qed.