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

Example test_case : is_simple_power_spec 8 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | [H | [H | H]]]].
    + discriminate.
    + destruct H; discriminate.
    + destruct H; discriminate.
    + destruct H; discriminate.
    + destruct H as [k [Hk1 [Hk2 Hk3]]].
      assert (k = 0 \/ k = 1 \/ k >= 2) as [K | [K | K]] by lia.
      * subst. simpl in Hk3. discriminate.
      * subst. simpl in Hk3. discriminate.
      * assert (5^2 <= 5^k).
        { apply Z.pow_le_mono_r; lia. }
        rewrite Hk3 in H. simpl in H. lia.
Qed.