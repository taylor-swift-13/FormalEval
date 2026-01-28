Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example problem_76_test_143214_16_false :
  problem_76_spec 143214%Z 16%Z false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [k Hk].
    exfalso.
    destruct k as [|k'].
    + simpl in Hk. compute in Hk. discriminate Hk.
    + rewrite Nat2Z.inj_succ in Hk.
      rewrite Z.pow_succ_r in Hk by apply Nat2Z.is_nonneg.
      apply f_equal with (f := fun t => t mod 16) in Hk.
      rewrite Z.mul_comm in Hk.
      rewrite Z_mod_mult in Hk.
      compute in Hk.
      discriminate Hk.
Qed.