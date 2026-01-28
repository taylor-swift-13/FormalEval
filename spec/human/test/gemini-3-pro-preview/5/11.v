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

Example test_case_2 : problem_5_spec [5; 10; 15] [5; 0; 10; 0; 15] 0.
Proof.
  unfold problem_5_spec.
  split.
  - intros Hempty.
    discriminate Hempty.
  - intros n Hlen Hn.
    simpl in Hlen.
    subst n.
    split.
    + reflexivity.
    + intros i Hi.
      split.
      * intros Heven.
        destruct i as [|i].
        { reflexivity. }
        destruct i as [|i].
        { exfalso. try unfold Nat.Even in Heven. try destruct Heven. try inversion Heven. lia. }
        destruct i as [|i].
        { reflexivity. }
        destruct i as [|i].
        { exfalso. try unfold Nat.Even in Heven. try destruct Heven. try inversion Heven. lia. }
        destruct i as [|i].
        { reflexivity. }
        exfalso; lia.
      * intros Hodd.
        destruct i as [|i].
        { exfalso. try unfold Nat.Odd in Hodd. try destruct Hodd. try inversion Hodd. lia. }
        destruct i as [|i].
        { reflexivity. }
        destruct i as [|i].
        { exfalso. try unfold Nat.Odd in Hodd. try destruct Hodd. try inversion Hodd. lia. }
        destruct i as [|i].
        { reflexivity. }
        destruct i as [|i].
        { exfalso. try unfold Nat.Odd in Hodd. try destruct Hodd. try inversion Hodd. lia. }
        exfalso; lia.
Qed.