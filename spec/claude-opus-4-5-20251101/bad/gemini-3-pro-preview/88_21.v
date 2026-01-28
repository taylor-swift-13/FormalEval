Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_sorted_ascending (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat ->
    nth i l 0 <= nth j l 0.

Definition is_sorted_descending (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat ->
    nth i l 0 >= nth j l 0.

Definition is_permutation (l1 l2 : list Z) : Prop :=
  forall x, count_occ Z.eq_dec l1 x = count_occ Z.eq_dec l2 x.

Definition sort_array_spec (array : list Z) (result : list Z) : Prop :=
  match array with
  | [] => result = []
  | [x] => result = [x]
  | _ =>
    let first := hd 0 array in
    let last := last array 0 in
    is_permutation array result /\
    (if Z.even (first + last)
     then is_sorted_descending result
     else is_sorted_ascending result)
  end.

Example test_sort_array_case1 : sort_array_spec [9; 7; 9] [9; 9; 7].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - unfold is_permutation. intros x. simpl.
    destruct (Z.eq_dec 9 x); destruct (Z.eq_dec 7 x); lia.
  - unfold is_sorted_descending.
    intros i j H_ij H_j_len.
    assert (Hi: (i = 0 \/ i = 1 \/ i = 2)%nat) by lia.
    assert (Hj: (j = 0 \/ j = 1 \/ j = 2)%nat) by lia.
    destruct Hi as [-> | [-> | ->]]; destruct Hj as [-> | [-> | ->]]; 
      simpl; try lia.
Qed.