Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_case : problem_76_spec 24 2 false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H. discriminate.
  - intros [k Hk].
    assert (H_cases: (k < 5 \/ 5 <= k)%nat) by lia.
    destruct H_cases as [H_lt | H_ge].
    + do 5 (destruct k as [|k]; [ simpl in Hk; discriminate | apply Nat.succ_lt_mono in H_lt ]).
      lia.
    + assert (H_pow: 2 ^ 5 <= 2 ^ (Z.of_nat k)).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow.
      rewrite <- Hk in H_pow.
      lia.
Qed.