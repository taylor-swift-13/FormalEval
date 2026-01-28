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

Example test_case : problem_5_spec [0; 0; 0] [0; 7; 0; 7; 0] 7.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case: input = [] -> output = [] *)
    intros H.
    discriminate H.
  - (* Case: Non-empty input constraints *)
    intros n Hlen Hn.
    simpl in Hlen.
    subst n.
    split.
    + (* Length check *)
      simpl. reflexivity.
    + (* Element check *)
      intros i Hi.
      split.
      * (* Even i *)
        intros Heven.
        destruct i.
        { (* i = 0 *) simpl. reflexivity. }
        destruct i.
        { (* i = 1 *) destruct Heven as [k Hk]. lia. }
        destruct i.
        { (* i = 2 *) simpl. reflexivity. }
        destruct i.
        { (* i = 3 *) destruct Heven as [k Hk]. lia. }
        destruct i.
        { (* i = 4 *) simpl. reflexivity. }
        lia. (* i >= 5 *)
      * (* Odd i *)
        intros Hodd.
        destruct i.
        { (* i = 0 *) destruct Hodd as [k Hk]. lia. }
        destruct i.
        { (* i = 1 *) simpl. reflexivity. }
        destruct i.
        { (* i = 2 *) destruct Hodd as [k Hk]. lia. }
        destruct i.
        { (* i = 3 *) simpl. reflexivity. }
        destruct i.
        { (* i = 4 *) destruct Hodd as [k Hk]. lia. }
        lia. (* i >= 5 *)
Qed.