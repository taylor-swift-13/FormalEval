Require Import List.
Require Import Arith.
Require Import Lia.
Require Import ZArith.
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

Example test_rolling_max_integers : rolling_max_spec 
  [-1%Z; -2%Z; -2%Z; -3%Z; -4%Z; -3%Z; -2%Z; -1%Z; -2%Z; -3%Z; -4%Z; -5%Z; -3%Z; -2%Z; -1%Z; 0%Z; -1%Z; -2%Z; -3%Z; -2%Z; -1%Z; 1%Z; 0%Z; -1%Z; -2%Z]
  [-1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.