Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 3 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk_ge_0 Heq]].
    assert (k < 2 \/ k >= 2) as [Hlt | Hge] by lia.
    + assert (k = 0 \/ k = 1) as [H0 | H1] by lia.
      * subst k. simpl in Heq. discriminate Heq.
      * subst k. simpl in Heq. discriminate Heq.
    + assert (2 ^ 2 <= 2 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      lia.
Qed.