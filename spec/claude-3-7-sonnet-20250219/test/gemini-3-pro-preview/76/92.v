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

Example test_case : is_simple_power_spec 37 15 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [H | [H | [H | [H | H]]]].
    + (* x = 1 *)
      lia.
    + (* n = 0 /\ x = 0 *)
      lia.
    + (* n = 1 /\ x = 1 *)
      lia.
    + (* n = -1 ... *)
      lia.
    + (* exists k ... *)
      destruct H as [k [Hk1 [Hk2 Hk3]]].
      assert (H_cases : k = 0 \/ k = 1 \/ k >= 2) by lia.
      destruct H_cases as [Hk0 | [Hk1' | Hk2']].
      * subst k. simpl in Hk3. lia.
      * subst k. simpl in Hk3. lia.
      * assert (H_mono : 15 ^ 2 <= 15 ^ k).
        { apply Z.pow_le_mono_r; lia. }
        simpl in H_mono. rewrite Hk3 in H_mono. lia.
Qed.