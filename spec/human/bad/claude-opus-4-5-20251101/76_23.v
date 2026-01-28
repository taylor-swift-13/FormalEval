Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_problem_76 : problem_76_spec 25%Z 23%Z false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H. discriminate.
  - intros [k Hk].
    destruct k as [|k'].
    + simpl in Hk. discriminate.
    + destruct k' as [|k''].
      * simpl in Hk. discriminate.
      * destruct k'' as [|k'''].
        -- simpl in Hk. discriminate.
        -- exfalso.
           assert (H1: 23 ^ 2 = 529) by reflexivity.
           assert (H2: 25 < 529) by lia.
           assert (H3: Z.of_nat (S (S (S k'''))) >= 2).
           { lia. }
           assert (H4: 23 ^ Z.of_nat (S (S (S k'''))) >= 23 ^ 2).
           { apply Z.pow_le_mono_r; lia. }
           lia.
Qed.