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

Example test_case : is_simple_power_spec 4 24 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    repeat destruct H as [H | H]; try lia.
    destruct H as [k [Hk1 [Hk2 Hk3]]].
    assert (k = 0 \/ k > 0) as [Hk0 | Hkpos] by lia.
    + subst. simpl in Hk3. discriminate.
    + assert (24 <= 24 ^ k).
      { change 24 with (24 ^ 1) at 1. apply Z.pow_le_mono_r; lia. }
      lia.
Qed.