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

Example test_case : is_simple_power_spec 10 81 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | [H | [H | [k [Hk [_ Heq]]]]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + assert (k = 0 \/ k > 0) as [Hk0 | Hkpos] by lia.
      * subst k. simpl in Heq. lia.
      * assert (81 ^ 1 <= 81 ^ k) as Hle.
        { apply Z.pow_le_mono_r; lia. }
        simpl in Hle. lia.
Qed.