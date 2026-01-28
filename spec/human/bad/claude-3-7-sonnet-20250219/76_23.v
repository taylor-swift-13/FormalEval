Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_case_25_23 :
  problem_76_spec 25 23 false.
Proof.
  unfold problem_76_spec.
  split.
  - intro H.
    discriminate H.
  - intro H.
    destruct H as [k Hk].
    discriminate H.
Qed.