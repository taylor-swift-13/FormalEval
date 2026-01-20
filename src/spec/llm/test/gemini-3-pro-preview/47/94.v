Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope Q_scope.

Definition median_spec (l : list Z) (res : Q) : Prop :=
  exists sorted_l,
    Permutation l sorted_l /\
    Sorted Z.le sorted_l /\
    let n := length l in
    (n > 0)%nat /\
    if Nat.odd n then
      res = inject_Z (nth (n / 2) sorted_l 0%Z)
    else
      res = Qdiv (Qplus (inject_Z (nth (n / 2 - 1) sorted_l 0%Z)) 
                        (inject_Z (nth (n / 2) sorted_l 0%Z))) 
                 (2#1).

Example test_median : median_spec [19; 7; 9; 3; 5]%Z (inject_Z 7).
Proof.
  unfold median_spec.
  exists [3; 5; 7; 9; 19]%Z.
  split.
  - (* Prove Permutation *)
    apply Permutation_trans with (l' := [7; 19; 9; 3; 5]%Z).
    + apply perm_swap.
    + apply Permutation_trans with (l' := [7; 9; 19; 3; 5]%Z).
      * apply perm_skip. apply perm_swap.
      * apply Permutation_trans with (l' := [7; 9; 3; 19; 5]%Z).
        -- do 2 apply perm_skip. apply perm_swap.
        -- apply Permutation_trans with (l' := [7; 9; 3; 5; 19]%Z).
           ++ do 3 apply perm_skip. apply perm_swap.
           ++ apply Permutation_trans with (l' := [7; 3; 9; 5; 19]%Z).
              ** apply perm_skip. apply perm_swap.
              ** apply Permutation_trans with (l' := [3; 7; 9; 5; 19]%Z).
                 --- apply perm_swap.
                 --- apply perm_skip.
                     apply Permutation_trans with (l' := [7; 5; 9; 19]%Z).
                     +++ apply perm_skip. apply perm_swap.
                     +++ apply Permutation_trans with (l' := [5; 7; 9; 19]%Z).
                         *** apply perm_swap.
                         *** apply perm_skip. reflexivity.
  - split.
    + (* Prove Sorted *)
      repeat constructor; try lia.
    + (* Prove Result *)
      split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.