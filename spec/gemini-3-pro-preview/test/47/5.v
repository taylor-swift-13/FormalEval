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

Example test_median : median_spec [8; 1; 3; 9; 9; 2; 7]%Z (inject_Z 7).
Proof.
  unfold median_spec.
  exists [1; 2; 3; 7; 8; 9; 9]%Z.
  split.
  - apply Permutation_trans with (l' := [1; 8; 3; 9; 9; 2; 7]%Z).
    + apply perm_swap.
    + apply perm_skip.
      apply Permutation_trans with (l' := [8; 3; 9; 2; 9; 7]%Z).
      * apply perm_skip; apply perm_skip; apply perm_skip; apply perm_swap.
      * apply Permutation_trans with (l' := [8; 3; 2; 9; 9; 7]%Z).
        { apply perm_skip; apply perm_skip; apply perm_swap. }
        apply Permutation_trans with (l' := [8; 2; 3; 9; 9; 7]%Z).
        { apply perm_skip; apply perm_swap. }
        apply Permutation_trans with (l' := [2; 8; 3; 9; 9; 7]%Z).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_trans with (l' := [3; 8; 9; 9; 7]%Z).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_trans with (l' := [8; 9; 7; 9]%Z).
        { apply perm_skip; apply perm_skip; apply perm_swap. }
        apply Permutation_trans with (l' := [8; 7; 9; 9]%Z).
        { apply perm_skip; apply perm_swap. }
        apply Permutation_trans with (l' := [7; 8; 9; 9]%Z).
        { apply perm_swap. }
        apply perm_skip.
        reflexivity.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.