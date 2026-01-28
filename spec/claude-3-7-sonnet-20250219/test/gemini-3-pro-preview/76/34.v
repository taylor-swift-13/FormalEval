Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (b : bool) : Prop :=
  b = true <->
    (x = 1) \/ 
    (n = 0 /\ x = 0) \/ 
    (n = 1 /\ x = 1) \/ 
    (n = -1 /\ (x = 1 \/ x = -1)) \/
    exists k : Z,
      (0 <= k) /\
      (Z.abs (Z.pow n k) <= Z.abs x) /\
      (Z.pow n k = x).

Example test_case : is_simple_power_spec 82 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H5 as [k [Hk_nonneg [Hk_bound Hk_eq]]].
      assert (k < 5).
      {
        assert (H_case: k < 5 \/ k >= 5) by lia.
        destruct H_case; auto.
        assert (H_pow: 3^5 <= 3^k).
        { apply Z.pow_le_mono_r; lia. }
        assert (H_calc: 3^5 = 243) by reflexivity.
        rewrite H_calc in H_pow.
        rewrite Hk_eq in H_pow.
        lia.
      }
      assert (H_vals: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
      destruct H_vals as [? | [? | [? | [? | ?]]]]; subst k;
      simpl in Hk_eq; try lia.
Qed.