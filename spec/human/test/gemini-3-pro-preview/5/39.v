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

Example test_case : problem_5_spec [-1; -2; -3] [-1; -4; -2; -4; -3] (-4).
Proof.
  unfold problem_5_spec.
  split.
  - intros H.
    discriminate H.
  - intros n Hlen Hn.
    simpl in Hlen.
    assert (n = 3%nat) by lia.
    subst n.
    split.
    + reflexivity.
    + intros i Hi.
      destruct i.
      * split.
        -- intros _. simpl. reflexivity.
        -- intros [k Hk]. lia.
      * destruct i.
        -- split.
           ++ intros [k Hk]. lia.
           ++ intros _. simpl. reflexivity.
        -- destruct i.
           ++ split.
              ** intros _. simpl. reflexivity.
              ** intros [k Hk]. lia.
           ++ destruct i.
              ** split.
                 --- intros [k Hk]. lia.
                 --- intros _. simpl. reflexivity.
              ** destruct i.
                 --- split.
                     +++ intros _. simpl. reflexivity.
                     +++ intros [k Hk]. lia.
                 --- lia.
Qed.