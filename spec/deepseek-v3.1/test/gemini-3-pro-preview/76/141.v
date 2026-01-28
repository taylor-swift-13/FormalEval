Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 3 65537 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Heq]].
    assert (k = 0 \/ k > 0) as [Hk0 | Hkpos] by lia.
    + subst k. simpl in Heq. discriminate.
    + assert (Hpow : 65537 ^ 1 <= 65537 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      lia.
Qed.