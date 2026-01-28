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

Example test_case : problem_5_spec [2; 4; 6; 8] [2; 1; 4; 1; 6; 1; 8] 1.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case: input = [] -> output = [] *)
    intros H. discriminate H.
  - (* Case: Non-empty input constraints *)
    intros n Hlen Hn.
    simpl in Hlen.
    subst n.
    split.
    + (* Length check *)
      simpl. reflexivity.
    + (* Element check *)
      intros i Hi.
      simpl in Hi.
      split.
      * (* Even i *)
        intros Heven.
        do 7 (destruct i as [|i]; [ 
          simpl; try reflexivity; exfalso; repeat inversion Heven 
        | ]).
        exfalso; lia.
      * (* Odd i *)
        intros Hodd.
        do 7 (destruct i as [|i]; [ 
          simpl; try reflexivity; exfalso; repeat inversion Hodd 
        | ]).
        exfalso; lia.
Qed.