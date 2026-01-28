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

Example problem_5_spec_case_single: problem_5_spec [3%Z] [3%Z] 1%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros n Hlen Hpos.
    simpl in Hlen.
    inversion Hlen. subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      assert (i = 0)%nat by lia.
      subst i.
      split.
      * intros _. replace (0 / 2)%nat with 0%nat by (apply Nat.div_small; lia).
        simpl. reflexivity.
      * intros Hodd. exfalso. destruct Hodd as [k Hk]. lia.
Qed.