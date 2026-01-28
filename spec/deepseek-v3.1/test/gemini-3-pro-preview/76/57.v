Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 125 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk_nonneg Hk_pow]].
    assert (H_cases: k < 7 \/ k >= 7) by lia.
    destruct H_cases as [H_small | H_large].
    + assert (H_vals: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
      destruct H_vals as [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]];
      simpl in Hk_pow; discriminate Hk_pow.
    + assert (H_mono: 2 ^ 7 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite Hk_pow in H_mono.
      lia.
Qed.