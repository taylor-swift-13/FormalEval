Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example problem_76_test : problem_76_spec 16 2 true.
Proof.
  unfold problem_76_spec.
  split.
  - intros _.
    exists 4%nat.
    simpl.
    reflexivity.
  - intros [k Hk].
    remember (Z.of_nat k) as zk.
    assert (Hzk: zk = 4).
    { rewrite <- Hk.
      rewrite Zpower_nat_Z.
      simpl.
      reflexivity.
    }
    subst zk.
    simpl in Hk.
    inversion Hk.
    reflexivity.
Qed.