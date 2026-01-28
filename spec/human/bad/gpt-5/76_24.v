Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example problem_76_test_23_2_false :
  problem_76_spec 23%Z 2%Z false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [k Hk].
    destruct k as [|k1].
    + simpl in Hk. change (2 ^ 0%Z) with 1%Z in Hk. exfalso. lia.
    + rewrite Z.of_nat_succ in Hk.
      rewrite Z.pow_add_r in Hk; try lia.
      change (2 ^ 1%Z) with 2%Z in Hk.
      set (t := 2 ^ Z.of_nat k1) in Hk.
      rewrite Z.mul_comm in Hk.
      exfalso. lia.
Qed.