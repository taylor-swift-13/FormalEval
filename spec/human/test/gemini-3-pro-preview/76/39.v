Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_case : problem_76_spec 15 23 false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H. inversion H.
  - intros [k Hk].
    destruct k.
    + simpl in Hk. discriminate.
    + assert (23 <= 23 ^ Z.of_nat (S k)).
      {
        change 23 with (23 ^ 1).
        apply Z.pow_le_mono_r; try lia.
      }
      rewrite <- Hk in H.
      lia.
Qed.