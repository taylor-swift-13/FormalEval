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

Example test_case : is_simple_power_spec 49 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    destruct H as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + (* x = 1 *)
      lia.
    + (* n = 0 /\ x = 0 *)
      lia.
    + (* n = 1 /\ x = 1 *)
      lia.
    + (* n = -1 ... *)
      lia.
    + (* exists k ... *)
      destruct H5 as [k [Hk1 [Hk2 Hk3]]].
      assert (k < 4 \/ k >= 4) by lia.
      destruct H as [Hsmall | Hlarge].
      * assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
        destruct H as [K0 | [K1 | [K2 | K3]]]; subst k; simpl in Hk3; lia.
      * assert (3 ^ 4 <= 3 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H.
        rewrite Hk3 in H.
        lia.
Qed.