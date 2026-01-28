Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_problem_76 : problem_76_spec 23%Z 2%Z false.
Proof.
  unfold problem_76_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k Hk].
    exfalso.
    destruct k as [|k'].
    + simpl in Hk. lia.
    + destruct k' as [|k''].
      * simpl in Hk. lia.
      * destruct k'' as [|k'''].
        -- simpl in Hk. lia.
        -- destruct k''' as [|k''''].
           ++ simpl in Hk. lia.
           ++ destruct k'''' as [|k'''''].
              ** simpl in Hk. lia.
              ** assert (2 ^ Z.of_nat (S (S (S (S (S k'''''))))) >= 32).
                 { assert (Z.of_nat (S (S (S (S (S k'''''))))) >= 5) by lia.
                   apply Z.ge_le in H.
                   apply Z.pow_le_mono_r with (a := 2) in H; lia. }
                 lia.
Qed.