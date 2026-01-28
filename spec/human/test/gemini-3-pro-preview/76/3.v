Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_case : problem_76_spec 4 2 true.
Proof.
  unfold problem_76_spec.
  split.
  - intros _.
    exists 2%nat.
    simpl.
    reflexivity.
  - intros _.
    reflexivity.
Qed.