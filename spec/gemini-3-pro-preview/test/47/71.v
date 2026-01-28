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

Example test_median : median_spec [2; 5; 40; 8; 11; 14]%Z (19#2).
Proof.
  unfold median_spec.
  exists [2; 5; 8; 11; 14; 40]%Z.
  split.
  - apply perm_skip. apply perm_skip.
    apply Permutation_trans with (l' := [8; 40; 11; 14]%Z).
    + apply perm_swap.
    + apply perm_skip.
      apply Permutation_trans with (l' := [11; 40; 14]%Z).
      * apply perm_swap.
      * apply perm_skip.
        apply perm_swap.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.