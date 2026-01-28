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

Example test_case : is_simple_power_spec 37 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros H.
    destruct H as [H | [H | [H | [H | H]]]].
    + discriminate.
    + destruct H; discriminate.
    + destruct H; discriminate.
    + destruct H as [H _]; discriminate.
    + destruct H as [k [Hk_ge0 [_ Hk_eq]]].
      assert (k < 3 \/ k >= 3) by lia.
      destruct H as [Hsmall | Hlarge].
      * assert (k = 0 \/ k = 1 \/ k = 2) by lia.
        destruct H as [K0 | [K1 | K2]]; subst k; simpl in Hk_eq; discriminate.
      * assert (6 ^ 3 <= 6 ^ k) as Hpow.
        { apply Z.pow_le_mono_r; lia. }
        simpl in Hpow.
        rewrite Hk_eq in Hpow.
        lia.
Qed.