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

Example test_case : problem_5_spec [1; 2; 3; 4] [1; 6; 2; 6; 3; 6; 4] 6.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate H.
  - intros n Hlen Hn.
    simpl in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      destruct i as [|i].
      { split.
        - intros _. reflexivity.
        - intros H. unfold Nat.Odd in H. destruct H. lia. }
      destruct i as [|i].
      { split.
        - intros H. unfold Nat.Even in H. destruct H. lia.
        - intros _. reflexivity. }
      destruct i as [|i].
      { split.
        - intros _. reflexivity.
        - intros H. unfold Nat.Odd in H. destruct H. lia. }
      destruct i as [|i].
      { split.
        - intros H. unfold Nat.Even in H. destruct H. lia.
        - intros _. reflexivity. }
      destruct i as [|i].
      { split.
        - intros _. reflexivity.
        - intros H. unfold Nat.Odd in H. destruct H. lia. }
      destruct i as [|i].
      { split.
        - intros H. unfold Nat.Even in H. destruct H. lia.
        - intros _. reflexivity. }
      destruct i as [|i].
      { split.
        - intros _. reflexivity.
        - intros H. unfold Nat.Odd in H. destruct H. lia. }
      lia.
Qed.