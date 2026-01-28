Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 49 82 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ 1 <= k) as [Hk0 | Hk1] by lia.
    + subst k. simpl in Heq. lia.
    + assert (82 ^ 1 <= 82 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      change (82 ^ 1) with 82 in Hpow.
      lia.
Qed.