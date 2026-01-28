Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_zeros: problem_3_spec [0; 0; 0; 0; 0] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    destruct prefix as [|z0 p0]; [simpl in Hlt; lia|].
    injection Heq as Hz0 Heq0; subst z0.
    destruct p0 as [|z1 p1]; [simpl in Hlt; lia|].
    injection Heq0 as Hz1 Heq1; subst z1.
    destruct p1 as [|z2 p2]; [simpl in Hlt; lia|].
    injection Heq1 as Hz2 Heq2; subst z2.
    destruct p2 as [|z3 p3]; [simpl in Hlt; lia|].
    injection Heq2 as Hz3 Heq3; subst z3.
    destruct p3 as [|z4 p4]; [simpl in Hlt; lia|].
    injection Heq3 as Hz4 Heq4; subst z4.
    destruct p4 as [|z5 p5]; [simpl in Hlt; lia|].
    discriminate Heq4.
  - intros H.
    discriminate H.
Qed.