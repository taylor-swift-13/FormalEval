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

Example test_case : is_simple_power_spec 4 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | [H | [H | H]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H as [k [Hk_ge_0 [Hbound Heq]]].
      assert (k = 0 \/ k > 0) as [Hk0 | Hk_pos] by lia.
      * subst k. simpl in Heq. lia.
      * assert (5 ^ 1 <= 5 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H. lia.
Qed.