Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 82 245 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k >= 1) as [Hk0 | Hk_ge_1] by lia.
    + subst k. simpl in Hk2. discriminate Hk2.
    + assert (Hpow: 245 ^ 1 <= 245 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      lia.
Qed.