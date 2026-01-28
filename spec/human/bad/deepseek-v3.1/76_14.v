Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Lemma problem_76_example : problem_76_spec 36 6 true.
Proof.
  unfold problem_76_spec.
  split.
  - intro H.
    exists 2%nat.
    compute. reflexivity.
  - intro H.
    destruct H as [k Hk].
    rewrite Hk.
    simpl.
    reflexivity.
Qed.