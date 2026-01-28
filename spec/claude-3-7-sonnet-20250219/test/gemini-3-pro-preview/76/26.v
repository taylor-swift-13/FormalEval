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

Example test_case : is_simple_power_spec 6 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros H.
    destruct H as [H | [H | [H | [H | H]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H as [k [Hk1 [Hk2 Hk3]]].
      assert (k < 2 \/ k >= 2) as [Hsmall | Hlarge] by lia.
      * assert (k = 0 \/ k = 1) as [K0 | K1] by lia.
        -- subst k. simpl in Hk3. discriminate.
        -- subst k. simpl in Hk3. discriminate.
      * assert (5^2 <= 5^k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H. rewrite Hk3 in H. lia.
Qed.