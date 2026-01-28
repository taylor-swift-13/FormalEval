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

Example test_case : is_simple_power_spec 19 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [H | [H | [H | [H | [k [Hk_pos [Hk_bound Hk_eq]]]]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + assert (k = 0 \/ k = 1 \/ k >= 2) by lia.
      destruct H as [K0 | [K1 | K2]].
      * subst k. simpl in Hk_eq. lia.
      * subst k. simpl in Hk_eq. lia.
      * assert (5 ^ 2 <= 5 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H. rewrite Hk_eq in H. lia.
Qed.