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

Example test_case : is_simple_power_spec 12 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros H.
    destruct H as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H5 as [k [Hk_ge_0 [Hk_bound Hk_eq]]].
      assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk | [Hk | Hk]] by lia.
      * subst k. simpl in Hk_eq. lia.
      * subst k. simpl in Hk_eq. lia.
      * assert (6 ^ 2 <= 6 ^ k) as Hpow.
        { apply Z.pow_le_mono_r; lia. }
        simpl in Hpow.
        rewrite Hk_eq in Hpow.
        lia.
Qed.