Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition list_max (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.max xs x
  end.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0 = list_max (firstn (i + 1)%nat numbers).

Example test_rolling_max_custom : rolling_max_spec 
  [-2; 5; 10; -1; -5; 20; 15; 6; 9; -8; -1; -5]
  [-2; 5; 10; 10; 10; 20; 20; 20; 20; 20; 20; 20].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 12 (destruct i as [|i]; [ simpl; reflexivity | simpl in H ]).
    lia.
Qed.