Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_case : problem_76_spec 12 6 false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    destruct k.
    + simpl in Hk. lia.
    + destruct k.
      * simpl in Hk. lia.
      * assert (Hgt: 6 ^ Z.of_nat (S (S k)) > 12).
        {
          replace (Z.of_nat (S (S k))) with (2 + Z.of_nat k) by lia.
          rewrite Z.pow_add_r; try lia.
          change (6^2) with 36.
          assert (Hge: 6 ^ Z.of_nat k >= 1).
          { apply Z.pow_ge_1; lia. }
          assert (36 * 1 <= 36 * 6 ^ Z.of_nat k).
          { apply Z.mul_le_mono_nonneg_l; lia. }
          lia.
        }
        rewrite <- Hk in Hgt.
        lia.
Qed.