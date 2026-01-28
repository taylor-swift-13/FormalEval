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

Example test_case : is_simple_power_spec 20 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | [H | [H | H]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H as [k [Hk_ge_0 [Hk_bound Hk_eq]]].
      assert (k < 2 \/ k >= 2) by lia.
      destruct H as [Hk_small | Hk_large].
      * assert (k = 0 \/ k = 1) by lia.
        destruct H as [Hk0 | Hk1].
        -- rewrite Hk0 in Hk_eq. simpl in Hk_eq. lia.
        -- rewrite Hk1 in Hk_eq. simpl in Hk_eq. lia.
      * assert (5 ^ 2 <= 5 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H.
        rewrite Hk_eq in H.
        lia.
Qed.