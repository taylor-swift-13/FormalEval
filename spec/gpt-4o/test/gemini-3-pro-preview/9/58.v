Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = 
            match firstn (i + 1)%nat numbers with
            | [] => 0
            | x :: xs => fold_left Z.max xs x
            end.

Example test_rolling_max_custom : rolling_max_spec [10; 5; 20; 30; 25; 20; 10; 21; 10; -1] [10; 10; 20; 30; 30; 30; 30; 30; 30; 30].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.