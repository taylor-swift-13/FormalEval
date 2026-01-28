Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Open Scope Z_scope.
Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> (1 <= n)%nat ->
      length output = (2 * n - 1)%nat /\
      forall i : nat, (i < 2 * n - 1)%nat ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example problem_5_pre_case_single: problem_5_pre [3%Z] [3%Z].
Proof.
  unfold problem_5_pre.
  exact I.
Qed.

Example problem_5_spec_case_single: problem_5_spec [3%Z] [3%Z] 0%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate H.
  - intros n Hlen Hpos.
    simpl in Hlen.
    subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      split.
      * intros Heven.
        assert (i = 0)%nat by lia.
        subst i.
        simpl.
        reflexivity.
      * intros Hodd.
        exfalso.
        assert (i = 0)%nat by lia.
        rewrite H in Hodd.
        destruct Hodd as [k Hk].
        lia.
Qed.