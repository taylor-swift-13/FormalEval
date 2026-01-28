Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition list_max_Z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.max xs x
  end.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0 = list_max_Z (firstn (i + 1)%nat numbers).

Example test_rolling_max_example : 
  rolling_max_spec [1; 2; -3; 4; 5; 4; 3; 2; 1] [1; 2; 2; 4; 5; 5; 5; 5; 5].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 9 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.