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

Example test_case : is_simple_power_spec 81 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [H | [H | [H | [H | [k [Hk1 [Hk2 Hk3]]]]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + assert (H_cases: k < 3 \/ k >= 3) by lia.
      destruct H_cases as [Hsmall | Hlarge].
      * assert (H_k: k = 0 \/ k = 1 \/ k = 2) by lia.
        destruct H_k as [E | [E | E]]; subst k; simpl in Hk3; lia.
      * assert (H_pow: 5^3 <= 5^k) by (apply Z.pow_le_mono_r; lia).
        simpl in H_pow.
        rewrite Hk3 in H_pow.
        lia.
Qed.