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

Example test_case : is_simple_power_spec 7 15 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    destruct H as [H | [H | [H | [H | H]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct H as [k [Hk1 [Hk2 Hk3]]].
      destruct k.
      * simpl in Hk3. lia.
      * assert (15 <= 15 ^ Z.pos p).
        { change 15 with (15^1). apply Z.pow_le_mono_r; lia. }
        lia.
      * lia.
Qed.