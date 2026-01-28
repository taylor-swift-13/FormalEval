Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 82 65 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (Hk_cases: k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct Hk_cases as [H0 | [H1 | H2]].
    + subst k. simpl in Hk2. discriminate.
    + subst k. simpl in Hk2. discriminate.
    + assert (Hle: 65 ^ 2 <= 65 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in Hle.
      change (65 ^ 2) with 4225 in Hle.
      lia.
Qed.