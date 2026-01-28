Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_case : problem_76_spec 25 6 false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H. discriminate.
  - intros [k Hk].
    destruct k.
    + simpl in Hk. discriminate.
    + destruct k.
      * simpl in Hk. discriminate.
      * destruct k.
        -- simpl in Hk. discriminate.
        -- assert (6 ^ 3 <= 6 ^ Z.of_nat (S (S (S k)))) as Hle.
           { apply Z.pow_le_mono_r; lia. }
           rewrite <- Hk in Hle.
           simpl in Hle.
           lia.
Qed.