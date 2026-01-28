Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0 = 
            match firstn (S i) numbers with
            | [] => 0
            | x :: xs => fold_left Z.max xs x
            end.

Example test_rolling_max_new : rolling_max_spec 
  [-1; -2; -3; -2; -3; -4; -3; -2; -1; -2; -3; -4; -5; -4; -3; -2; 9; -1; 0; -1; -2; -3; -2; 0; 1; 0; -1; -2] 
  [-1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; 9; 9; 9; 9; 9; 9; 9; 9; 9; 9; 9; 9].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 28 (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    lia.
Qed.