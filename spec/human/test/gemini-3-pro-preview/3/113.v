Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1000000; -500000; -500000; 1000000] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    destruct prefix as [|x1 t1]; [simpl in Hlt; lia|].
    simpl in Heq. injection Heq as Hx1 Heq1. subst x1.
    destruct t1 as [|x2 t2]; [simpl in Hlt; lia|].
    simpl in Heq1. injection Heq1 as Hx2 Heq2. subst x2.
    destruct t2 as [|x3 t3]; [simpl in Hlt; lia|].
    simpl in Heq2. injection Heq2 as Hx3 Heq3. subst x3.
    destruct t3 as [|x4 t4]; [simpl in Hlt; lia|].
    simpl in Heq3. injection Heq3 as Hx4 Heq4. subst x4.
    destruct t4 as [|x5 t5]; [simpl in Hlt; lia|].
    simpl in Heq4. discriminate.
  - intros H. discriminate H.
Qed.