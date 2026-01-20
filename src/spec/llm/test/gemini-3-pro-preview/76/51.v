Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 64 21 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (H : k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H as [H0 | [H1 | H2]].
    + subst k. simpl in Hk2. discriminate.
    + subst k. simpl in Hk2. discriminate.
    + assert (Hpow : 21 ^ 2 <= 21 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      change (21 ^ 2) with 441 in Hpow.
      lia.
Qed.