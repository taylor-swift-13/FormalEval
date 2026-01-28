Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Lra.

Import ListNotations.
Local Open Scope R_scope.

Definition problem_20_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_20_spec (input : list R) (output1 output2 : R) : Prop :=
  (length input >= 2)%nat /\
  In output1 input /\
  In output2 input /\
  output1 <= output2 /\
  (forall i j : nat,
    (i < length input)%nat ->
    (j < length input)%nat ->
    i <> j ->
    Rabs (output1 - output2) <= Rabs (nth i input 0 - nth j input 0)).

Example test_case_20 : 
  problem_20_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 3.9 4.0.
Proof.
  unfold problem_20_spec.
  repeat split.
  - simpl. lia.
  - simpl. right. right. left. reflexivity.
  - simpl. right. right. right. left. reflexivity.
  - lra.
  - intros i j Hi Hj Hneq.
    simpl in Hi, Hj.
    assert (Hbound_i: (i <= 5)%nat) by lia.
    assert (Hbound_j: (j <= 5)%nat) by lia.
    do 6 (destruct i as [|i]; [|try (do 6 (destruct j as [|j]; 
        [|try (exfalso; lia)]))]);
    do 6 (destruct j as [|j]; [|try (exfalso; lia)]);
    try (exfalso; apply Hneq; reflexivity).
    all: compute; lra.
Qed.