Require Import List.
Require Import Arith.
Require Import Lia.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0%Z = 
            match firstn (i + 1)%nat numbers with
            | [] => 0%Z
            | h :: t => fold_left Z.max t h
            end.

Example test_rolling_max_integers : 
  rolling_max_spec 
    [4%Z; -3%Z; -4%Z; -5%Z; -4%Z; -3%Z; -2%Z; -2%Z; -3%Z; 3%Z] 
    [4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.