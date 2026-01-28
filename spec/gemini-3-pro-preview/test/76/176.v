Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 4722366482869645213695 4722366482869645213697 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Heq]].
    set (n := 4722366482869645213697) in *.
    set (x := 4722366482869645213695) in *.
    assert (Hn_pos : 0 < n).
    { subst n. reflexivity. }
    assert (Hx_lt_n : x < n).
    { subst x n. reflexivity. }
    destruct (Z.eq_dec k 0) as [Hk0 | Hk_neq0].
    + subst k. rewrite Z.pow_0_r in Heq.
      subst x. discriminate.
    + assert (Hk_ge_1 : 1 <= k) by lia.
      assert (Hpow : n ^ 1 <= n ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Z.pow_1_r in Hpow.
      rewrite <- Heq in Hpow.
      lia.
Qed.