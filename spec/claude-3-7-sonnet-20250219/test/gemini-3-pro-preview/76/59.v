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

Example test_case : is_simple_power_spec 8 64 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros H_rhs.
    destruct H_rhs as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + discriminate H1.
    + destruct H2 as [_ Hx]. discriminate Hx.
    + destruct H3 as [_ Hx]. discriminate Hx.
    + destruct H4 as [Hn _]. discriminate Hn.
    + destruct H5 as [k [Hk_ge_0 [_ Hk_eq]]].
      assert (Hk_cases: k = 0 \/ 1 <= k) by lia.
      destruct Hk_cases as [Hk0 | Hk1].
      * subst k. simpl in Hk_eq. discriminate Hk_eq.
      * assert (H_pow: 64 ^ 1 <= 64 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H_pow.
        rewrite Hk_eq in H_pow.
        lia.
Qed.