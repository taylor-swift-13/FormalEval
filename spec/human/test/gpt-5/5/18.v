Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> 1 <= n ->
      length output = 2 * n - 1 /\
      forall i : nat, i < 2 * n - 1 ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example problem_5_test_single :
  problem_5_spec [3%Z] [3%Z] 1%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. inversion H.
  - intros n Hlen Hle.
    simpl in Hlen.
    symmetry in Hlen.
    subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      destruct i as [|i'].
      * split.
        -- intros _. simpl. reflexivity.
        -- intros Hodd. destruct Hodd as [k Hk]. lia.
      * assert (False) by (simpl in Hi; lia).
        split; intros _; exfalso; assumption.
Qed.