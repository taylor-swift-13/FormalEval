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

Example test_case : is_simple_power_spec 8 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | [H | [H | H]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H as [k [Hk_ge0 [Hk_abs Hk_eq]]].
      assert (Hk_cases: k = 0 \/ k = 1 \/ k >= 2) by lia.
      destruct Hk_cases as [Hk0 | [Hk1 | Hk2]].
      * subst k. simpl in Hk_eq. lia.
      * subst k. simpl in Hk_eq. lia.
      * assert (H_mono: 6 ^ 2 <= 6 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H_mono.
        rewrite Hk_eq in H_mono.
        lia.
Qed.