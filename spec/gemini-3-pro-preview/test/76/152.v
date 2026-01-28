Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 6 4722366482869645213696 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Heq]].
    remember 4722366482869645213696 as n.
    assert (Hn : n > 6).
    { subst n. reflexivity. }
    destruct (Z.eq_dec k 0) as [Hk0 | Hk_neq].
    + subst k. rewrite Z.pow_0_r in Heq. discriminate Heq.
    + assert (Hk_ge_1 : k >= 1) by lia.
      assert (Hpow : n <= n ^ k).
      { rewrite <- (Z.pow_1_r n) at 1. apply Z.pow_le_mono_r; lia. }
      lia.
Qed.