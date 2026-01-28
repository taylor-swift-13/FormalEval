Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example problem_76_test_16_2_true :
  problem_76_spec 16%Z 2%Z true.
Proof.
  unfold problem_76_spec.
  split.
  - intros _.
    exists 4%nat.
    simpl.
    change (16%Z = 2 ^ 4%Z).
    compute.
    reflexivity.
  - intros _.
    reflexivity.
Qed.