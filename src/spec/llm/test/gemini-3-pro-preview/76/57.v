Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 125 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros H. destruct H as [k [Hk Heq]].
    assert (H_cases: k < 7 \/ k >= 7) by lia.
    destruct H_cases as [Hlt | Hge].
    + assert (Hpow: 2 ^ k <= 2 ^ 6).
      { apply Z.pow_le_mono_r; lia. }
      replace (2 ^ 6) with 64 in Hpow by reflexivity.
      lia.
    + assert (Hpow: 2 ^ 7 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      replace (2 ^ 7) with 128 in Hpow by reflexivity.
      lia.
Qed.