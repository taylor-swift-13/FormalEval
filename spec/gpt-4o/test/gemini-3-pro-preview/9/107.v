Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            let prefix := firstn (i + 1) numbers in
            nth i result 0 = fold_left Z.max (tl prefix) (hd 0 prefix).

Example test_rolling_max_custom : rolling_max_spec 
  [-1%Z; -2%Z; -3%Z; -2%Z; -3%Z; -4%Z; -3%Z; -2%Z; -1%Z; -2%Z; -3%Z; -4%Z; -5%Z; -4%Z; -3%Z; -2%Z; -1%Z; 0%Z; -1%Z; -2%Z; -3%Z; -2%Z; -1%Z; 0%Z; 1%Z; 0%Z; -1%Z; -2%Z]
  [-1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - reflexivity.
  - intros i H.
    do 28 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.