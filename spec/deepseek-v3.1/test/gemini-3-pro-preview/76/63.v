Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 125 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hge Hpow]].
    assert (H_cases: k < 3 \/ k >= 3) by lia.
    destruct H_cases as [H_small | H_large].
    + assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [E | [E | E]]; subst k; simpl in Hpow; discriminate.
    + assert (H_mono: 6 ^ 3 <= 6 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite Hpow in H_mono.
      lia.
Qed.