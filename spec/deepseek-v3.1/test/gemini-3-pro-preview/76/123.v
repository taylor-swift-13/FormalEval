Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 65537 65536 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk Hpow]].
    assert (k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H as [H | [H | H]].
    + rewrite H in Hpow. simpl in Hpow. discriminate.
    + rewrite H in Hpow. simpl in Hpow. discriminate.
    + assert (65536 ^ 2 <= 65536 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hpow in H0.
      simpl in H0.
      lia.
Qed.