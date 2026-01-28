Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 8 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as Hcases by lia.
    destruct Hcases as [Hk0 | [Hk1_eq | Hk2_ge]].
    + subst k. simpl in Hk2. lia.
    + subst k. simpl in Hk2. lia.
    + assert (5 ^ 2 <= 5 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in Hpow.
      simpl in Hpow.
      lia.
Qed.