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

Example test_median : median_spec [13; 0; 0; 1; 1; 0]%Z (1#2).
Proof.
  unfold median_spec.
  exists [0; 0; 0; 1; 1; 13]%Z.
  split.
  - apply Permutation_trans with (l' := [0; 13; 0; 1; 1; 0]%Z).
    + apply perm_swap.
    + apply perm_skip.
      apply Permutation_trans with (l' := [0; 13; 1; 1; 0]%Z).
      * apply perm_swap.
      * apply perm_skip.
        apply Permutation_trans with (l' := [13; 1; 0; 1]%Z).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [13; 0; 1; 1]%Z).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [0; 13; 1; 1]%Z).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_trans with (l' := [1; 13; 1]%Z).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.