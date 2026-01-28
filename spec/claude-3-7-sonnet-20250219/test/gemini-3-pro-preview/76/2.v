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

Example test_case : is_simple_power_spec 143214 16 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [H | [H | [H | [H | H]]]].
    + inversion H.
    + destruct H; inversion H.
    + destruct H; inversion H.
    + destruct H; inversion H.
    + destruct H as [k [Hk1 [Hk2 Hk3]]].
      assert (k < 5 \/ k >= 5) as [Hsmall | Hlarge] by lia.
      * assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
        destruct H as [| [| [| [|]]]]; subst k; simpl in Hk3; discriminate.
      * assert (16^5 <= 16^k) by (apply Z.pow_le_mono_r; lia).
        simpl in H. rewrite Hk3 in H. lia.
Qed.