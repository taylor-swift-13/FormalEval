Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) 0%Z.

Open Scope Z_scope.

Example test_rolling_max_integers : 
  rolling_max_spec [0; 4; -3; -4; -5; -4; -3; -2; -1] 
                   [0; 4; 4; 4; 4; 4; 4; 4; 4].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.