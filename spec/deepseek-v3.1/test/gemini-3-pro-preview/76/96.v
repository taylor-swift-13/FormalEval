Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 82 23 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k < 2 \/ k >= 2) as [Hlt | Hge] by lia.
    + assert (k = 0 \/ k = 1) as [K0 | K1] by lia.
      * subst k. simpl in Hk2. discriminate.
      * subst k. simpl in Hk2. discriminate.
    + assert (23 ^ 2 <= 23 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in H.
      change (23 ^ 2) with 529 in H.
      lia.
Qed.