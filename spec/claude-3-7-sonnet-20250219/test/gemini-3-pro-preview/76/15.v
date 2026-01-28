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

Example test_case : is_simple_power_spec 10 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | [H | [H | H]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H as [k [Hk1 [Hk2 Hk3]]].
      assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ 4 <= k) as [ | [ | [ | [ | ]]]] by lia.
      * subst. simpl in Hk3. lia.
      * subst. simpl in Hk3. lia.
      * subst. simpl in Hk3. lia.
      * subst. simpl in Hk3. lia.
      * assert (Hge: 2 ^ 4 <= 2 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in Hge. rewrite Hk3 in Hge. lia.
Qed.