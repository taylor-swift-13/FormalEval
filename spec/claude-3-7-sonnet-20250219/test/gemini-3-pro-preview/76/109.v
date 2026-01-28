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

Example test_case : is_simple_power_spec 4722366482869645213696 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [H | [H | [H | [H | H]]]].
    + discriminate.
    + destruct H; discriminate.
    + destruct H; discriminate.
    + destruct H; discriminate.
    + destruct H as [k [Hk_nonneg [_ Hk_eq]]].
      assert (H_cases : k <= 27 \/ 28 <= k) by lia.
      destruct H_cases as [H_le | H_ge].
      * assert (H_pow : 6^k <= 6^27).
        { apply Z.pow_le_mono_r; lia. }
        rewrite Hk_eq in H_pow.
        apply Z.leb_le in H_pow.
        vm_compute in H_pow.
        discriminate.
      * assert (H_pow : 6^28 <= 6^k).
        { apply Z.pow_le_mono_r; try lia. }
        rewrite Hk_eq in H_pow.
        apply Z.leb_le in H_pow.
        vm_compute in H_pow.
        discriminate.
Qed.