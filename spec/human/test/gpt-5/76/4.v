Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example problem_76_test_9_3_true :
  problem_76_spec 9%Z 3%Z true.
Proof.
  unfold problem_76_spec.
  split.
  - intros _.
    exists 2%nat.
    simpl.
    change (9%Z = 3 ^ 2%Z).
    compute.
    reflexivity.
  - intros _.
    reflexivity.
Qed.