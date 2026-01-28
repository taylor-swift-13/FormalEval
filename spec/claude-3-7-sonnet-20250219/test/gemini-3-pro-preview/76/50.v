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

Example test_case : is_simple_power_spec 83 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    (* We assume the disjunction holds and derive a contradiction *)
    destruct H as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + (* Case x = 1 *)
      lia.
    + (* Case n = 0 /\ x = 0 *)
      lia.
    + (* Case n = 1 /\ x = 1 *)
      lia.
    + (* Case n = -1 ... *)
      lia.
    + (* Case exists k ... *)
      destruct H5 as [k [Hk_ge_0 [Habs Heq]]].
      (* We have 4^k = 83. We split cases on k. *)
      assert (k < 4 \/ k >= 4) as [Hsmall | Hlarge] by lia.
      * (* Case k < 4: check k = 0, 1, 2, 3 *)
        assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as Hk_cases by lia.
        destruct Hk_cases as [K | [K | [K | K]]]; subst k; simpl in Heq; lia.
      * (* Case k >= 4: 4^k >= 4^4 = 256 > 83 *)
        assert (Hpow: 4^4 <= 4^k).
        { apply Z.pow_le_mono_r; lia. }
        rewrite Heq in Hpow.
        simpl in Hpow.
        lia.
Qed.