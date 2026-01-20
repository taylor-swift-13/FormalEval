Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
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

Example test_sort_1234 : sort_array_spec [1; 2; 3; 4] [1; 2; 3; 4].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - unfold is_permutation.
    intro x.
    reflexivity.
  - unfold is_sorted_ascending.
    intros i j Hij Hj.
    simpl in Hj.
    destruct i as [|i'].
    + destruct j as [|j'].
      * lia.
      * destruct j' as [|j''].
        -- simpl. lia.
        -- destruct j'' as [|j'''].
           ++ simpl. lia.
           ++ destruct j''' as [|j''''].
              ** simpl. lia.
              ** simpl in Hj. lia.
    + destruct i' as [|i''].
      * destruct j as [|j'].
        -- lia.
        -- destruct j' as [|j''].
           ++ lia.
           ++ destruct j'' as [|j'''].
              ** simpl. lia.
              ** destruct j''' as [|j''''].
                 --- simpl. lia.
                 --- simpl in Hj. lia.
      * destruct i'' as [|i'''].
        -- destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** lia.
              ** destruct j'' as [|j'''].
                 --- lia.
                 --- destruct j''' as [|j''''].
                    +++ simpl. lia.
                    +++ simpl in Hj. lia.
        -- destruct i''' as [|i''''].
           ++ destruct j as [|j'].
              ** lia.
              ** destruct j' as [|j''].
                 --- lia.
                 --- destruct j'' as [|j'''].
                     +++ lia.
                     +++ destruct j''' as [|j''''].
                         *** lia.
                         *** simpl in Hj. lia.
           ++ simpl in Hij. lia.
Qed.