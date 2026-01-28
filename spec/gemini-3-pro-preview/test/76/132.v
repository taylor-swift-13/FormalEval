Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 82 245 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk Heq]].
    assert (Hk_cases: k = 0 \/ k >= 1) by lia.
    destruct Hk_cases as [Hk0 | Hk1].
    + subst k.
      simpl in Heq.
      discriminate Heq.
    + assert (Hle: 245 ^ 1 <= 245 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hle.
      rewrite <- Heq in Hle.
      lia.
Qed.