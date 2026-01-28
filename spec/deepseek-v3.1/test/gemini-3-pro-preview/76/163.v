Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4 16777216 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (H_cases: k = 0 \/ k >= 1) by lia.
    destruct H_cases as [Hk0 | Hk_ge_1].
    + subst k.
      simpl in Hk2.
      discriminate Hk2.
    + assert (H_mono: 16777216 ^ 1 <= 16777216 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in H_mono.
      simpl in H_mono.
      lia.
Qed.