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

Example test_case : is_simple_power_spec 10 11 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    destruct H as [H | [H | [H | [H | H]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H as [k [Hk_pos [Hk_bound Hk_eq]]].
      assert (Hk_cases : k = 0 \/ 0 < k) by lia.
      destruct Hk_cases as [Hk0 | Hk_gt_0].
      * subst k. simpl in Hk_eq. lia.
      * assert (11 <= 11 ^ k).
        {
          rewrite <- (Z.pow_1_r 11) at 1.
          apply Z.pow_le_mono_r; lia.
        }
        lia.
Qed.