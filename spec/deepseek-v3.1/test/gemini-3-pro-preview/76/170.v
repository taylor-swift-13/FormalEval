Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 82 4722366482869645213696 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (Hk : k = 0 \/ k >= 1) by lia.
    destruct Hk as [Hk0 | Hk_ge_1].
    + subst k. simpl in Hk2. discriminate.
    + assert (Hge : 4722366482869645213696 ^ 1 <= 4722366482869645213696 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Z.pow_1_r in Hge.
      rewrite Hk2 in Hge.
      lia.
Qed.