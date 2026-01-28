Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 82 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (H_cases: k < 4 \/ k = 4 \/ k > 4) by lia.
    destruct H_cases as [Hlt | [Heq | Hgt]].
    + assert (Hpow: 3 ^ k < 3 ^ 4).
      { apply Z.pow_lt_mono_r; lia. }
      rewrite <- Hk2 in Hpow.
      simpl in Hpow.
      lia.
    + rewrite Heq in Hk2.
      simpl in Hk2.
      lia.
    + assert (Hpow: 3 ^ 5 <= 3 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in Hpow.
      simpl in Hpow.
      lia.
Qed.