Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example problem_76_test_5_5_true :
  problem_76_spec 5%Z 5%Z true.
Proof.
  unfold problem_76_spec.
  split.
  - intros _.
    exists 1%nat.
    simpl.
    change (5%Z = 5 ^ 1%Z).
    compute.
    reflexivity.
  - intros _.
    reflexivity.
Qed.