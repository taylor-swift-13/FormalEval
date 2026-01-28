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

Example test_case : is_simple_power_spec 23 81 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + discriminate H1.
    + destruct H2 as [Hn Hx]. discriminate Hn.
    + destruct H3 as [Hn Hx]. discriminate Hn.
    + destruct H4 as [Hn Hx]. discriminate Hn.
    + destruct H5 as [k [Hk_ge_0 [Habs Hpow]]].
      destruct (Z.eq_dec k 0) as [Heq | Hneq].
      * subst k. simpl in Hpow. discriminate Hpow.
      * assert (Hk : k >= 1) by lia.
        assert (Hmono : 81 ^ 1 <= 81 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in Hmono.
        rewrite Hpow in Hmono.
        lia.
Qed.